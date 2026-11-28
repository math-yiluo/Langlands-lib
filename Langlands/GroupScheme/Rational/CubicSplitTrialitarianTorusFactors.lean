import Langlands.GroupScheme.Rational.CubicSplitPinningTypeA2
import Langlands.GroupScheme.Rational.CyclicD4A2TorusProduct
import Langlands.GroupScheme.Rational.TrialitarianOppositeBorelFactorsProof

/-! # Inner type-A2 factors of the supplied cubic-split trialitarian torus -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1200000
set_option maxRecDepth 4000

variable {F K : Type u} [Field F] [Field K] [Algebra F K]
  [FiniteDimensional F K] [IsGalois F K]
  {G : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
  {T : CommGroupScheme (Spec (CommRingCat.of F))}

local notation "S" => Spec (CommRingCat.of F)
local notation "BC" => CommGroupScheme.baseChange (algebraBaseMap F K)

/-- A supplied cubic-split maximal torus of an anisotropic simply connected
D4 group factors through two actual inner A2 subgroups. The second factor
acts by conjugation on the first group and fixes its torus. -/
theorem exists_cubicSplitTrialitarianTorusFactors
    (d : TitsIndexData G) (e : d.Vertex ≃ Fin 4)
    (hD : ∀ a c, d.cartan a c = CartanMatrix.D 4 (e a) (e c))
    (hsc : IsSimplyConnected G) (han : IsAnisotropic G) (hdeg : Module.finrank F K = 3)
    (t : T.toGrp ⟶ G) (ht : IsMaximalTorus t) (hT : IsSplitTorus ((BC).obj T).toGrp) :
    ∃ (T₁ T₂ : CommGroupScheme S) (H₁ H₂ : GroupScheme S)
      (_ : IsAffineHom H₁.X.hom) (_ : LocallyOfFiniteType H₁.X.hom)
      (_ : IsAffineHom H₂.X.hom) (_ : LocallyOfFiniteType H₂.X.hom)
      (d₁ : TitsIndexData H₁) (d₂ : TitsIndexData H₂)
      (p₁ : T.toGrp ⟶ T₁.toGrp) (p₂ : T.toGrp ⟶ T₂.toGrp)
      (i₁ : T₁.toGrp ⟶ H₁) (i₂ : T₂.toGrp ⟶ H₂) (j₁ : H₁ ⟶ G) (j₂ : H₂ ⟶ G)
      (act : AutomorphicAction T₂.toGrp H₁),
      IsMaximalTorus i₁ ∧ IsMaximalTorus i₂ ∧
      IsSplitTorus ((BC).obj T₁).toGrp ∧ IsSplitTorus ((BC).obj T₂).toGrp ∧
      IsSimplyConnected H₁ ∧ IsAbsolutelyAlmostSimple H₁ ∧ d₁.HasInnerTypeA 2 ∧
      IsSimplyConnected H₂ ∧ IsAbsolutelyAlmostSimple H₂ ∧ d₂.HasInnerTypeA 2 ∧
      (∀ (Z : Over S) (x : Z ⟶ T₂.toGrp.X) (y : Z ⟶ H₁.X),
        act.act x y ≫ j₁.hom.hom = (x ≫ (i₂ ≫ j₂).hom.hom) *
          (y ≫ j₁.hom.hom) * (x ≫ (i₂ ≫ j₂).hom.hom)⁻¹) ∧
      (∀ (Z : Over S) (x : Z ⟶ T₂.toGrp.X) (z : Z ⟶ T₁.toGrp.X),
        act.act x (z ≫ i₁.hom.hom) = z ≫ i₁.hom.hom) ∧
      ∀ (Z : Over S) (z : Z ⟶ T.toGrp.X), z ≫ t.hom.hom =
        ((z ≫ p₁.hom.hom ≫ i₁.hom.hom) ≫ j₁.hom.hom) *
          ((z ≫ p₂.hom.hom) ≫ (i₂ ≫ j₂).hom.hom) := by
  let emb : K →ₐ[F] SeparableClosure F := IsSepClosed.lift
  let : Algebra K (SeparableClosure F) := emb.toRingHom.toAlgebra
  let : IsScalarTower F K (SeparableClosure F) :=
    IsScalarTower.of_algebraMap_eq fun x => (emb.commutes x).symm
  obtain ⟨p, eT, heT⟩ :=
    exists_galoisPinning_of_splitMaximalTorus hsc.isSemisimple.isConnectedReductive t ht hT
  have hp : IsMaximalTorus p.inclusion := by
    rw [← heT]
    exact ht.iso_comp (CartanConjugacyDensity.groupIso eT)
  obtain ⟨v, hv, _⟩ := p.exists_titsVertexComparison d
  let q := v.trans e
  have hq (a c : p.base.support) :
      p.rootDatum.pairing a.val c.val = CartanMatrix.D 4 (q a) (q c) :=
    (hv a c).trans (hD (v a) (v c))
  obtain ⟨D⟩ := p.nonempty_cyclicD4A2TorusFactors hsc hp han hdeg q hq
  let A := D.first
  let B := D.second
  let C := A.groups
  let E := B.groups
  let : IsAffineHom C.derived.X.hom := C.derivedAffine
  let : LocallyOfFiniteType C.derived.X.hom := C.derivedFiniteType
  let : IsAffineHom E.derived.X.hom := E.derivedAffine
  let : LocallyOfFiniteType E.derived.X.hom := E.derivedFiniteType
  let : IsAffineHom C.levi.X.hom := C.isReductive.isAffineHom
  have hA (a c : A.roots.face.base.support) :
      A.roots.rootDatum.pairing a.val c.val = CartanMatrix.A 2 (A.simple.symm a) (A.simple.symm c) := by
    simpa only [Equiv.apply_symm_apply] using A.cartan (A.simple.symm a) (A.simple.symm c)
  have hB (a c : B.roots.face.base.support) :
      B.roots.rootDatum.pairing a.val c.val = CartanMatrix.A 2 (B.simple.symm a) (B.simple.symm c) := by
    simpa only [Equiv.apply_symm_apply] using B.cartan (B.simple.symm a) (B.simple.symm c)
  obtain ⟨d₁, ha₁, hA₁⟩ :=
    A.roots.pinning.exists_innerTypeA2_of_cubicPinning C.isSimplyConnected hdeg A.simple.symm hA
  obtain ⟨d₂, ha₂, hA₂⟩ :=
    B.roots.pinning.exists_innerTypeA2_of_cubicPinning E.isSimplyConnected hdeg B.simple.symm hB
  let j₁ := C.derivedInclusion ≫ C.inclusion
  let j₂ := E.derivedInclusion ≫ E.inclusion
  have h₁ : C.torusInclusion ≫ j₁ = CommGroupScheme.groupHom C.torusMap ≫ p.inclusion := by
    dsimp only [j₁]
    rw [← Category.assoc, C.torus_square, Category.assoc, C.leviTorus_comp]
  have h₂ : E.torusInclusion ≫ j₂ = CommGroupScheme.groupHom E.torusMap ≫ p.inclusion := by
    dsimp only [j₂]
    rw [← Category.assoc, E.torus_square, Category.assoc, E.leviTorus_comp]
  obtain ⟨p₁, p₂, hprod⟩ :=
    exists_torusFactorProjections t p.inclusion eT heT C.torusMap E.torusMap D.product_isIso
  obtain ⟨act, hact, hfix⟩ := exists_derivedFaceAction C.leviTorusInclusion C.inclusion
    C.derivedInclusion C.isDerived C.torusInclusion C.torusMap E.torusMap C.torus_square E.torus_maximal.1
  refine ⟨C.torus, E.torus, C.derived, E.derived, inferInstance, inferInstance, inferInstance,
    inferInstance, d₁, d₂, p₁, p₂, C.torusInclusion, E.torusInclusion, j₁, j₂, act,
    C.torus_maximal, E.torus_maximal, A.roots.isSplit, B.roots.isSplit,
    C.isSimplyConnected, ha₁, hA₁, E.isSimplyConnected, ha₂, hA₂, ?_, hfix, ?_⟩
  · intro Z x y
    rw [h₂]
    simpa only [Category.assoc, C.leviTorus_comp] using hact Z x y
  · intro Z z
    have h₁' : (CommGroupScheme.groupHom C.torusMap ≫ p.inclusion).hom.hom =
        C.torusInclusion.hom.hom ≫ j₁.hom.hom :=
      (congrArg (fun f : C.torus.toGrp ⟶ G => f.hom.hom) h₁).symm
    simpa only [h₁', ← h₂, Category.assoc] using hprod Z z

end Langlands.GroupScheme
