import Langlands.GroupScheme.Rational.AnisotropicCyclicTorusNorm
import Langlands.GroupScheme.Rational.GaloisBorelFaceRoots
import Langlands.GroupScheme.Rational.GaloisPinningCorootAction
import Langlands.GroupScheme.Torus.MultiplicativeTypeSubgroups
import Langlands.GroupScheme.Torus.RelativeDiagonalizableSplit
import Langlands.GroupScheme.Torus.RelativeFieldComparison
import Langlands.LinearAlgebra.TypeD4CyclicA2Face

/-! # A descended type-A2 derived group for a cyclic D4 root pair -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open Langlands.LinearAlgebra Langlands.LinearAlgebra.RootDatumZeroFace

namespace Langlands.GroupScheme

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 950000
set_option maxRecDepth 3000

variable {F K : Type u} [Field F] [Field K] [Algebra F K]
  {G : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom] (p : GaloisPinningData F K G)

local notation "b" => algebraBaseMap F K
local notation "BG" => GroupScheme.baseChange b
local notation "BC" => CommGroupScheme.baseChange b
local notation "TE" => Functor.obj BC p.torus

omit [LocallyOfFiniteType G.X.hom] in
/-- Change the simple base while retaining the same split maximal torus and root datum. -/
abbrev GaloisPinningData.withSimpleBase (B : p.rootDatum.Base) : GaloisPinningData F K G :=
  { p with
    base := B
    pinning := RootPinning.ofSplitMaximalTorus p.isConnectedReductive p.isSplitTorus
      _ p.isMaximalTorus p.rootDatum p.isRootDatum B }

variable [FiniteDimensional F K] [IsGalois F K]

/-- The coroots of a torus in an anisotropic group sum to zero along each
orbit of the generator of a cubic splitting field. -/
theorem GaloisPinningData.coroot_cyclic_norm_eq_zero
    (ht : IsMaximalTorus p.inclusion) (hG : IsAnisotropic G) (hdeg : Module.finrank F K = 3)
    (σ : K ≃ₐ[F] K) (hσ : orderOf σ = 3) (i : p.rootIndex) :
    let s := (p.galoisAction σ).indexEquiv
    p.rootDatum.coroot i + p.rootDatum.coroot (s i) + p.rootDatum.coroot (s (s i)) = 0 := by
  let : IsAffine p.torus.X.left := SplittingAssembly.isAffine_of_isTorus _ ht.1
  let : IsAffineHom p.torus.X.hom := inferInstance
  have h := hG.cocharacter_cyclic_norm_eq_zero ht.2.1 hdeg σ hσ (p.rootDatum.coroot i)
  rw [← p.galoisAction_coroot σ, ← p.galoisAction_coroot (σ ^ 2), map_pow, pow_two] at h
  exact h

omit [FiniteDimensional F K] [IsGalois F K] in
/-- The ordinary root action of the cubic generator has cube equal to the identity. -/
theorem GaloisPinningData.cyclic_rootIndex_cube
    (σ : K ≃ₐ[F] K) (hσ : orderOf σ = 3) (i : p.rootIndex) :
    let s := (p.galoisAction σ).indexEquiv
    s (s (s i)) = i := by
  have h : σ ^ 3 = 1 := hσ ▸ pow_orderOf_eq_one σ
  have hg : (p.galoisAction σ) ^ 3 = 1 := by rw [← map_pow, h, map_one]
  exact congrArg (fun a : p.rootDatum.Aut => a.indexEquiv i) hg

omit [FiniteDimensional F K] [IsGalois F K] in
/-- The linear equivalence whose action on coroots advances their indices. -/
theorem GaloisPinningData.galoisAction_coweightEquiv_symm_coroot
    (σ : K ≃ₐ[F] K) (i : p.rootIndex) :
    (p.galoisAction σ).symm.coweightEquiv (p.rootDatum.coroot i) =
      p.rootDatum.coroot ((p.galoisAction σ).indexEquiv i) :=
  (p.galoisAction σ).symm.coroot_coweightMap_apply p.rootDatum p.rootDatum i

omit [FiniteDimensional F K] [IsGalois F K] in
private theorem isSplitTorus_of_closedSubgroup_splitTorus
    {U V : GroupScheme (Spec (CommRingCat.of K))}
    (hU : IsTorus U) (hV : IsSplitTorus V) (j : U ⟶ V) (hj : IsClosedSubgroup j) :
    IsSplitTorus U := by
  obtain ⟨Λ, hΛ, hfg, ⟨e⟩⟩ := exists_diagonalizableIso_of_isClosedSubgroup_splitTorus hV j hj
  let : AddCommGroup Λ := hΛ
  exact hU.isRelativeTorus.isSplitTorus_of_isDiagonalizable
    ⟨Λ, hΛ, hfg, ⟨e ≪≫ (Diagonalizable.baseChangeIso (Gm.toSpecZ _) Λ).symm⟩⟩

omit [FiniteDimensional F K] [IsGalois F K] in
/-- A descended derived Levi indexed by an ordered A2 pair. Its maximal torus
and its two coroots retain their embeddings into the original group. -/
structure CyclicD4A2DerivedFace (i j : p.rootIndex) where
  base : p.rootDatum.Base
  direction : cocharacterLattice (TE)
  groups : GaloisBorelFaceDerived (p.withSimpleBase base) direction
  roots : groups.RootModel
  simple : Fin 2 ≃ roots.face.base.support
  simple_first : (roots.simpleEquiv (simple 0)).val.val = i
  simple_second : (roots.simpleEquiv (simple 1)).val.val = j
  cartan : ∀ k l, roots.rootDatum.pairing (simple k).val (simple l).val = CartanMatrix.A 2 k l

include p in
private theorem cyclic_d4_coroot_face_stable
    (ht : IsMaximalTorus p.inclusion) (han : IsAnisotropic G)
    (hdeg : Module.finrank F K = 3) (σ : K ≃ₐ[F] K) (hσ : orderOf σ = 3)
    (i : p.rootIndex) :
    let s := (p.galoisAction σ).indexEquiv
    ∀ (τ : K ≃ₐ[F] K) (a : p.rootIndex),
      (p.galoisAction τ).indexEquiv a ∈ d4A2CorootSet p.rootDatum i (s i) ↔
        a ∈ d4A2CorootSet p.rootDatum i (s i) := by
  intro s τ a
  have hs := mem_d4A2CorootSet_cyclic_iff p.rootDatum s
    (p.cyclic_rootIndex_cube σ hσ) (p.coroot_cyclic_norm_eq_zero ht han hdeg σ hσ)
    (p.galoisAction σ).symm.coweightEquiv (p.galoisAction_coweightEquiv_symm_coroot σ) i
  obtain ⟨n, rfl⟩ := (cubic_aut_pow_bijective hdeg σ hσ).surjective τ
  rw [map_pow]
  generalize (n : ℕ) = m
  induction m with
  | zero => rw [pow_zero]; rfl
  | succ m ih =>
    rw [pow_succ']
    exact (hs _).trans ih

omit [FiniteDimensional F K] [IsGalois F K] in
private def twoSimpleZeroRootEquiv (ν : cocharacterLattice (TE)) (B : p.rootDatum.Base)
    (i j : p.rootIndex) (hne : i ≠ j)
    (h : ∀ k : p.rootIndex, k ∈ B.support ∧ p.rootDatum.root' k ν = 0 ↔ k = i ∨ k = j) :
    Fin 2 ≃ {a : B.support // p.rootDatum.root' a.val ν = 0} := by
  classical
  let u : {a : B.support // p.rootDatum.root' a.val ν = 0} :=
    ⟨⟨i, ((h i).mpr (Or.inl rfl)).1⟩, ((h i).mpr (Or.inl rfl)).2⟩
  let v : {a : B.support // p.rootDatum.root' a.val ν = 0} :=
    ⟨⟨j, ((h j).mpr (Or.inr rfl)).1⟩, ((h j).mpr (Or.inr rfl)).2⟩
  refine ⟨![u, v], fun a => if a.val.val = i then 0 else 1, ?_, ?_⟩
  · intro a
    fin_cases a <;> simp [u, v, hne.symm]
  · intro a
    rcases (h a.val.val).mp ⟨a.val.property, a.property⟩ with ha | ha
    · simp only [ha, ite_true, Matrix.cons_val_zero]
      exact Subtype.ext (Subtype.ext ha.symm)
    · simp only [ha, hne.symm, ite_false, Matrix.cons_val_one]
      exact Subtype.ext (Subtype.ext ha.symm)

/-- The actual centralizer of a cyclic A2 zero face and its derived group
descend together with the induced torus split by the cubic field. -/
theorem GaloisPinningData.nonempty_cyclicD4A2DerivedFace
    (hsc : IsSimplyConnected G) (ht : IsMaximalTorus p.inclusion) (han : IsAnisotropic G)
    (hdeg : Module.finrank F K = 3) (e : p.base.support ≃ Fin 4)
    (hD : ∀ v w : p.base.support, p.rootDatum.pairing v.val w.val = CartanMatrix.D 4 (e v) (e w))
    (σ : K ≃ₐ[F] K) (hσ : orderOf σ = 3) (i : p.rootIndex) :
    Nonempty (CyclicD4A2DerivedFace p i ((p.galoisAction σ).indexEquiv i)) := by
  let j := (p.galoisAction σ).indexEquiv i
  let : p.rootDatum.IsReduced := p.isReduced
  have hspan := p.corootSpan_eq_top_of_simplyConnected hsc
  have hp := pairing_cyclic_eq_neg_one p.rootDatum p.base hspan e hD
    (p.galoisAction σ).indexEquiv (fun a c => (p.galoisAction σ).toHom.pairing)
    (p.cyclic_rootIndex_cube σ hσ) (p.coroot_cyclic_norm_eq_zero ht han hdeg σ hσ) i
  change p.rootDatum.pairing i j = -1 at hp
  have hne : i ≠ j := by
    intro h
    rw [← h, p.rootDatum.pairing_same] at hp
    omega
  obtain ⟨ν, B, hν, hpos, hzero⟩ := exists_d4A2_basedZeroFace p.rootDatum p.base hspan e hD i j hp
  let q := p.withSimpleBase B
  have hstable (τ : K ≃ₐ[F] K) : SubgroupFunctor.galoisTransport F K G τ
      (Dynamic.centralizer (CommGroupScheme.groupHom ν ≫ (BG).map q.inclusion)) =
        Dynamic.centralizer (CommGroupScheme.groupHom ν ≫ (BG).map q.inclusion) := by
    apply q.galoisTransport_centralizer_of_stable_zeroRoots τ ν
    intro a
    change p.rootDatum.root' ((p.galoisAction τ).indexEquiv a) ν = 0 ↔
      p.rootDatum.root' a ν = 0
    rw [hν, hν]
    exact cyclic_d4_coroot_face_stable p ht han hdeg σ hσ i τ a
  obtain ⟨D⟩ := exists_galoisBorelFaceDerived_of_invariantCentralizer q hsc ht ν hstable
  have hT : IsSplitTorus ((BC).obj D.torus).toGrp :=
    isSplitTorus_of_closedSubgroup_splitTorus (D.torus_maximal.1.baseChange (K := K))
      p.isSplitTorus ((BG).map (CommGroupScheme.groupHom D.torusMap))
      (D.torusMap_closed.baseChange b)
  obtain ⟨R⟩ := D.nonempty_rootModel hT (fun a => hpos a.val a.property)
  let d := twoSimpleZeroRootEquiv p ν B i j hne hzero
  let f := d.trans R.simpleEquiv.symm
  have hf (k : Fin 2) : R.simpleEquiv (f k) = d k := R.simpleEquiv.apply_symm_apply _
  have hf₀ : (R.simpleEquiv (f 0)).val.val = i :=
    (congrArg (fun a => a.val.val) (hf 0)).trans rfl
  have hf₁ : (R.simpleEquiv (f 1)).val.val = j :=
    (congrArg (fun a => a.val.val) (hf 1)).trans rfl
  have hp' : p.rootDatum.pairing j i = -1 := by
    change p.rootDatum.root' j (p.rootDatum.coroot i) = -1
    rw [← d4CorootCoordinates_dotProduct_coroot p.rootDatum p.base hspan e hD,
      dotProduct_comm, d4CorootCoordinates_dotProduct_coroot p.rootDatum p.base hspan e hD]
    exact hp
  refine ⟨⟨B, ν, D, R, f, hf₀, hf₁, ?_⟩⟩
  intro k l
  rw [R.face.pairing_eq]
  change p.rootDatum.pairing (R.simpleEquiv (f k)).val.val (R.simpleEquiv (f l)).val.val = _
  fin_cases k <;> fin_cases l <;>
    set_option backward.isDefEq.respectTransparency false in
    norm_num [hf₀, hf₁, hp, hp', CartanMatrix.A, Matrix.of_apply]

end Langlands.GroupScheme
