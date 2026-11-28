import Langlands.GroupScheme.Reductive.StarActionFiniteStageLift
import Langlands.GroupScheme.Reductive.StarOrbitRootSums
import Langlands.GroupScheme.Reductive.TitsIndexExistenceProof
import Langlands.GroupScheme.Reductive.SeparablyClosedAlmostSimpleAbsoluteProof
import Langlands.GroupScheme.Rational.SimpleBaseFactorSurjectivity
import Langlands.GroupScheme.SimplyConnected.InnerTypeANormOneStatement
import Langlands.GroupScheme.Torus.MultiplicativeTypeAbsoluteEquivalenceProof
import Mathlib.Data.Fintype.Perm

/-! # The absolute and inner types of a group with a cubic-split type-A2 torus -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Langlands.LinearAlgebra

namespace Langlands.GroupScheme

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1000000
set_option maxRecDepth 3500

section Pinning

variable {F K : Type u} [Field F] [Field K] [Algebra F K]
  {G : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]

local notation "b" => algebraBaseMap F K

/-- Build a pinning on the extension of the given maximal torus. -/
theorem exists_galoisPinning_of_splitMaximalTorus
    (hG : IsConnectedReductive G) {T : CommGroupScheme (Spec (CommRingCat.of F))}
    (t : T.toGrp ⟶ G) (ht : IsMaximalTorus t)
    (hs : IsSplitTorus ((CommGroupScheme.baseChange b).obj T).toGrp) :
    ∃ (p : GaloisPinningData F K G) (e : p.torus ≅ T),
      CommGroupScheme.groupHom e.hom ≫ t = p.inclusion := by
  let H := (GroupScheme.baseChange b).obj G
  let A := (CommGroupScheme.baseChange b).obj T
  let i := (GroupScheme.baseChange b).map t
  let : Smooth G.X.hom := hG.smooth
  let : IsAffineHom H.X.hom :=
    inferInstanceAs (IsAffineHom (CategoryTheory.Limits.pullback.snd G.X.hom b))
  let : LocallyOfFiniteType H.X.hom :=
    inferInstanceAs (LocallyOfFiniteType (CategoryTheory.Limits.pullback.snd G.X.hom b))
  have hH := connectedReductiveFieldExtensionStatement F K G hG
  have hi := (maximalTorusBaseChange F K G T t ht.1 ht.2.1).mp ht
  obtain ⟨I, hI, P, hP, hred⟩ := rootDatumExistence K H hH A hs i hi
  let : Finite I := hI
  let : P.IsReduced := hred
  let B := Langlands.LinearAlgebra.RootDatumBase.base P
  let p : GaloisPinningData F K G :=
    { torus := T
      inclusion := t
      isConnectedReductive := hH
      isSplitTorus := hs
      isMaximalTorus := hi
      rootIndex := I
      finiteRootIndex := hI
      rootDatum := P
      isRootDatum := hP
      isReduced := hred
      base := B
      pinning := RootPinning.ofSplitMaximalTorus hH hs i hi P hP B }
  exact ⟨p, Iso.refl _, Category.id_comp t⟩

variable [FiniteDimensional F K] [IsGalois F K]

omit [FiniteDimensional F K] in
/-- A finite-stage pinning gives the Cartan matrix and full star permutation
of any actual Tits index, using the restriction to its splitting field. -/
theorem GaloisPinningData.exists_titsVertexComparison
    [Algebra K (SeparableClosure F)] [IsScalarTower F K (SeparableClosure F)]
    (p : GaloisPinningData F K G) (d : TitsIndexData G) :
    ∃ v : p.base.support ≃ d.Vertex,
      (∀ a c, p.rootDatum.pairing a.val c.val = d.cartan (v a) (v c)) ∧
      ∀ (τ : SeparableClosure F ≃ₐ[F] SeparableClosure F) a,
        v (p.starSupport (τ.restrictNormal K) a) = d.star τ (v a) := by
  obtain ⟨q, e, hbase, hstar⟩ := StarActionFiniteStage.exists_lift p
    (MultiplicativeTypeAbsoluteEquivalence.algebraBaseMap_tower K (SeparableClosure F))
  obtain ⟨_, _, f, _, _, hf, hfstar⟩ :=
    StarActionIndependence.starActionIndependence F (SeparableClosure F) G q d.pinning
  let e₁ := e.indexEquiv.subtypeEquiv hbase
  let e₂ := f.indexEquiv.subtypeEquiv hf
  let v : p.base.support ≃ d.Vertex := e₁.trans e₂
  refine ⟨v, fun a c => e.toHom.pairing.symm.trans f.toHom.pairing.symm, ?_⟩
  intro τ a
  have he :=
    congrArg (fun g => g.indexEquiv a.val)
      (hstar (τ.restrictNormal K) τ fun x => (τ.restrictNormal_commutes K x).symm)
  have hq :=
    congrArg (fun g => g.indexEquiv (e.indexEquiv a.val)) (hfstar τ)
  apply Subtype.ext
  change f.indexEquiv (e.indexEquiv ((p.starAction (τ.restrictNormal K)).val.indexEquiv a.val)) =
    (d.pinning.starAction τ).val.indexEquiv (f.indexEquiv (e.indexEquiv a.val))
  change e.indexEquiv ((p.starAction (τ.restrictNormal K)).val.indexEquiv a.val) =
    (q.starAction τ).val.indexEquiv (e.indexEquiv a.val) at he
  rw [he]
  exact hq

end Pinning

section Star

variable {F K : Type u} [Field F] [Field K] [Algebra F K]
  {G : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
  (p : GaloisPinningData F K G)

private def starPermutation : (K ≃ₐ[F] K) →* Equiv.Perm p.base.support where
  toFun σ :=
    { toFun := p.starSupport σ
      invFun := p.starSupport σ⁻¹
      left_inv := p.starSupport_inv_starSupport σ
      right_inv := fun a => by
        rw [← p.starSupport_mul, mul_inv_cancel, p.starSupport_one] }
  map_one' := Equiv.ext p.starSupport_one
  map_mul' σ τ := Equiv.ext (p.starSupport_mul σ τ)

/-- A cubic Galois action fixes the two simple vertices of an A2 pinning. -/
theorem GaloisPinningData.starSupport_eq_self_of_cubic_two_vertices
    [FiniteDimensional F K] [IsGalois F K]
    (hdeg : Module.finrank F K = 3) (e : p.base.support ≃ Fin 2)
    (σ : K ≃ₐ[F] K) (a : p.base.support) : p.starSupport σ a = a := by
  classical
  let : Fintype p.base.support := Fintype.ofFinite _
  have hcard : Nat.card (Equiv.Perm p.base.support) = 2 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_congr e, Fintype.card_fin]
    decide
  have h₂ := orderOf_dvd_natCard (starPermutation p σ)
  rw [hcard] at h₂
  have h₃ := (orderOf_map_dvd (starPermutation p) σ).trans (orderOf_dvd_natCard σ)
  rw [IsGalois.card_aut_eq_finrank F K, hdeg] at h₃
  have h : orderOf (starPermutation p σ) ∣ 1 := Nat.dvd_gcd h₂ h₃
  have hs : starPermutation p σ = 1 := orderOf_eq_one_iff.mp (Nat.dvd_one.mp h)
  exact congrArg (fun θ : Equiv.Perm p.base.support => θ a) hs

end Star

section TypeA

variable {F K : Type u} [Field F] [Field K] [Algebra F K]
  {G : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]

/-- A simply connected group whose absolute Cartan matrix is A2 is
absolutely almost simple. Its two vertices belong to one geometric factor. -/
theorem TitsIndexData.isAbsolutelyAlmostSimple_of_CartanA2 (d : TitsIndexData G)
    (hsc : IsSimplyConnected G) (e : d.Vertex ≃ Fin 2)
    (hcartan : ∀ a c, d.cartan a c = CartanMatrix.A 2 (e a) (e c)) :
    IsAbsolutelyAlmostSimple G := by
  let E := SeparableClosure F
  let HE := (GroupScheme.baseChange (algebraBaseMap F E)).obj G
  let : IsAffineHom HE.X.hom :=
    inferInstanceAs (IsAffineHom (CategoryTheory.Limits.pullback.snd G.X.hom (algebraBaseMap F E)))
  let : LocallyOfFiniteType HE.X.hom :=
    inferInstanceAs (LocallyOfFiniteType (CategoryTheory.Limits.pullback.snd G.X.hom
      (algebraBaseMap F E)))
  let sc := isSimplyConnectedFieldExtension F E G hsc
  let hD := sc.isSemisimple
  let D := sc.almostSimpleProduct
  let p := d.pinning.toSplitPinning
  let f (a : d.Vertex) := D.rootDatumFactorIndex hD p.isSplitTorus
    p.inclusion p.isMaximalTorus p.isRootDatum a.val
  let a := e.symm 0
  let i := f a
  have hconn (v : d.Vertex) : f v = i := by
    by_cases hv : v = a
    · exact congrArg f hv
    · apply (D.rootDatumFactorIndex_eq_iff_cartanConnected hD p v a).mpr
      apply Relation.EqvGen.rel
      refine ⟨hv, ?_⟩
      change d.cartan v a ≠ 0
      have h₀ : e a = 0 := e.apply_symm_apply 0
      have h₁ : e v = 1 := by
        have hne : e v ≠ 0 := fun h => hv (e.injective (h.trans h₀.symm))
        exact Fin.eq_one_of_ne_zero (e v) hne
      rw [hcartan, h₁, h₀]
      decide
  have hall (j : D.Index) : j = i := by
    obtain ⟨v, rfl⟩ := D.rootDatumFactorIndex_surjective_on_base hD p j
    exact hconn v
  let g : HE ≅ D.factor i :=
    { hom := D.projection i
      inv := D.inclusion i
      hom_inv_id := by
        apply (cancel_mono D.iso.hom).mp
        apply Pi.hom_ext
        intro j
        obtain rfl := hall j
        simp only [SimplyConnectedAlmostSimpleProduct.projection,
          SimplyConnectedAlmostSimpleProduct.inclusion, Category.assoc,
          Iso.inv_hom_id_assoc, piFactorInclusionHom_π_self, Category.comp_id,
          Category.id_comp]
      inv_hom_id := D.inclusion_projection i }
  exact IsAbsolutelyAlmostSimple.of_fieldExtension (K := E)
    (separablyClosedAlmostSimpleAbsolute E HE ((D.isAlmostSimple i).of_iso g))

variable [FiniteDimensional F K] [IsGalois F K]

/-- A simply connected group with a cubic-split maximal torus of Cartan type
A2 is absolutely almost simple and has an inner type-A2 index. -/
theorem GaloisPinningData.exists_innerTypeA2_of_cubicPinning
    (p : GaloisPinningData F K G) (hsc : IsSimplyConnected G)
    (hdeg : Module.finrank F K = 3) (e : p.base.support ≃ Fin 2)
    (hcartan : ∀ a c : p.base.support, p.rootDatum.pairing a.val c.val = CartanMatrix.A 2 (e a) (e c)) :
    ∃ d : TitsIndexData G, IsAbsolutelyAlmostSimple G ∧ d.HasInnerTypeA 2 := by
  let j : K →ₐ[F] SeparableClosure F := IsSepClosed.lift
  let : Algebra K (SeparableClosure F) := j.toRingHom.toAlgebra
  let : IsScalarTower F K (SeparableClosure F) :=
    IsScalarTower.of_algebraMap_eq fun x => (j.commutes x).symm
  obtain ⟨d⟩ := titsIndexExistence F G hsc.isSemisimple
  obtain ⟨v, hv, hstar⟩ := p.exists_titsVertexComparison d
  let w := v.symm.trans e
  have hD (a c : d.Vertex) : d.cartan a c = CartanMatrix.A 2 (w a) (w c) := by
    simpa only [Equiv.apply_symm_apply, w, Equiv.trans_apply] using
      (hv (v.symm a) (v.symm c)).symm.trans (hcartan (v.symm a) (v.symm c))
  refine ⟨d, d.isAbsolutelyAlmostSimple_of_CartanA2 hsc w hD, by decide, ⟨w, hD⟩, ?_⟩
  intro τ a
  obtain ⟨c, rfl⟩ := v.surjective a
  rw [← hstar τ c, p.starSupport_eq_self_of_cubic_two_vertices hdeg e (τ.restrictNormal K) c]

end TypeA

end Langlands.GroupScheme
