import Langlands.AbelianScheme.Tate.TwoPowerTorsionClosure
import Langlands.AbelianScheme.Tate.TwoPowerTorsionClosureConnectedStatement
import Langlands.AlgebraicGeometry.LocallyNoetherianConnectedComponentOpenProof
import Mathlib.Topology.Connected.TotallyDisconnected
import Mathlib.Logic.Function.Iterate

/-! # Connectedness of the actual two-power torsion closure -/

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open scoped CategoryTheory.MonObj

namespace Langlands.AbelianScheme.Tate

universe u

private theorem connectedSpace_of_dense_eventually_fixed
    {X : Type*} [TopologicalSpace X] [NoetherianSpace X]
    (f : X → X) (hf : Continuous f) (hsurj : Function.Surjective f)
    (e : X) (he : f e = e) (T : Set X) (hT : Dense T)
    (hkill : ∀ x ∈ T, ∃ n : ℕ, f^[n] x = e) : ConnectedSpace X := by
  classical
  let : DiscreteTopology (ConnectedComponents X) :=
    ConnectedComponents.discreteTopology_iff.mpr fun x =>
      Langlands.AlgebraicGeometry.isOpen_connectedComponent_of_noetherianSpace x
  let : Finite (ConnectedComponents X) := finite_of_compact_of_discrete
  let g := hf.connectedComponentsMap
  have hginj : Function.Injective g :=
    Finite.injective_iff_surjective.mpr (hf.connectedComponentsMap_surjective hsurj)
  have hiter (n : ℕ) (x : X) :
      g^[n] (ConnectedComponents.mk x) = ConnectedComponents.mk (f^[n] x) := by
    induction n with
    | zero => rfl
    | succ n ih =>
      rw [Function.iterate_succ_apply', ih, Function.iterate_succ_apply']
      exact hf.connectedComponentsMap_mk _
  have hfixed (n : ℕ) : f^[n] e = e := by
    induction n with
    | zero => rfl
    | succ n ih => rw [Function.iterate_succ_apply', ih, he]
  have hsub : T ⊆ connectedComponent e := by
    intro x hx
    obtain ⟨n, hn⟩ := hkill x hx
    apply ConnectedComponents.coe_eq_coe'.mp
    apply hginj.iterate n
    rw [hiter, hiter, hn, hfixed]
  apply connectedSpace_iff_connectedComponent.mpr
  refine ⟨e, Set.eq_univ_of_forall fun x => ?_⟩
  exact (closure_minimal hsub isClosed_connectedComponent) (hT x)

variable {K : Type u} [Field K]
  (A : AbelianScheme (Spec (CommRingCat.of K)))

/-- Iterating actual multiplication by two on a section evaluates its
`2^n`-th power. -/
theorem multiplication_two_iterate_section (n : ℕ)
    (s : Over.mk (𝟙 (Spec (CommRingCat.of K))) ⟶ A.X) :
    ((GroupScheme.multiplication A.toGrp (2 : ℤ)).hom.hom.left : A.X.left → A.X.left)^[n]
      (s.left (default : Spec (CommRingCat.of K))) =
        (s ^ (2 ^ n)).left (default : Spec (CommRingCat.of K)) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply', ih, ← pow_two_section_apply, ← pow_mul, ← pow_succ]

variable [IsAlgClosed K] [CharZero K]

/-- The actual Zariski closure of geometric two-power torsion is connected. -/
theorem isConnected_closure_twoPowerTorsionLocus :
    _root_.IsConnected (closure (twoPowerTorsionLocus A)) := by
  have : CompactSpace A.X.left := QuasiCompact.compactSpace_of_compactSpace A.X.hom
  have : IsLocallyNoetherian A.X.left := LocallyOfFiniteType.isLocallyNoetherian A.X.hom
  have : IsNoetherian A.X.left := {}
  let T := twoPowerTorsionLocus A
  let C := closure T
  let f : A.X.left → A.X.left :=
    (GroupScheme.multiplication A.toGrp (2 : ℤ)).hom.hom.left
  have hf : Continuous f :=
    (GroupScheme.multiplication A.toGrp (2 : ℤ)).hom.hom.left.continuous
  have himage : f '' C = C := image_closure_twoPowerTorsionLocus_multiplication_two A
  have hmap : Set.MapsTo f C C := by
    intro x hx
    rw [← himage]
    exact Set.mem_image_of_mem f hx
  let F : C → C := fun x => ⟨f x.1, hmap x.2⟩
  have hF : Continuous F := (hf.comp continuous_subtype_val).subtype_mk _
  have hFsurj : Function.Surjective F := by
    intro x
    have hx : x.1 ∈ f '' C := by rw [himage]; exact x.2
    obtain ⟨y, hy, hxy⟩ := hx
    exact ⟨⟨y, hy⟩, Subtype.ext hxy⟩
  let s : Over.mk (𝟙 (Spec (CommRingCat.of K))) ⟶ A.X := 1
  let e := s.left (default : Spec (CommRingCat.of K))
  have heT : e ∈ T := ⟨0, s, by simp [s], rfl⟩
  let E : C := ⟨e, subset_closure heT⟩
  have hFE : F E = E := by
    apply Subtype.ext
    change f e = e
    dsimp only [f, e]
    rw [← pow_two_section_apply A s]
    simp [s]
  have hiter (n : ℕ) (x : C) : (F^[n] x).1 = f^[n] x.1 := by
    induction n with
    | zero => rfl
    | succ n ih => rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ← ih]
  have hTdense : Dense (Subtype.val ⁻¹' T : Set C) := by
    apply Subtype.dense_iff.mpr
    have himg : Subtype.val '' (Subtype.val ⁻¹' T : Set C) = T := by
      ext x
      constructor
      · rintro ⟨y, hy, rfl⟩
        exact hy
      · intro hx
        exact ⟨⟨x, subset_closure hx⟩, hx, rfl⟩
    rw [himg]
  have : ConnectedSpace C :=
    connectedSpace_of_dense_eventually_fixed F hF hFsurj E hFE _ hTdense (by
      rintro x ⟨n, t, ht, htx⟩
      refine ⟨n, Subtype.ext ?_⟩
      rw [hiter, ← htx, multiplication_two_iterate_section, ht])
  exact isConnected_iff_connectedSpace.mpr this

/-- The actual two-power torsion closure is connected over every
algebraically closed characteristic-zero field. -/
theorem twoPowerTorsionClosureConnected :
    TwoPowerTorsionClosureConnectedStatement.{u} := by
  intro K _ _ _ A
  exact isConnected_closure_twoPowerTorsionLocus A

end Langlands.AbelianScheme.Tate
