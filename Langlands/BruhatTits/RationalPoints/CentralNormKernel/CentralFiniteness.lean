import Langlands.GroupScheme.Derived.CentralIntersection.AlgClosed
import Langlands.GroupScheme.SchemeActionFiniteTarget

/-! # Finiteness of central subgroups with root-of-unity eigenvalues

Over an algebraically closed field, let `s : S ⟶ G` be a closed central subgroup of an affine
group scheme of finite type with trivial unipotent radical, and `ρ` a closed linear embedding of
`G` such that every eigenvalue of every rational point of `S` is an `m`-th root of unity. The
identity component of the reduced subgroup of `S` is then smooth, connected, central and
unipotent, hence trivial; so `S` has finitely many points and finitely many rational points.
This is the argument of `CentralIntersection.exists_isClosed_isOpen_singleton` with its
eigenvalue input made a hypothesis. -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.CartesianMonoidalCategory
  AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme Langlands.GroupScheme.CentralIntersection

namespace Langlands.BruhatTits.RationalPoints.CentralNormKernel

variable {K : Type u} [Field K] [IsAlgClosed K]

/-- A closed central subgroup whose rational points have root-of-unity eigenvalues in a closed
linear embedding has an isolated closed point. -/
theorem exists_isClosed_isOpen_singleton_of_eigenvalues
    {G S : GroupScheme (Spec (CommRingCat.of K))} (s : S ⟶ G) [IsAffine G.X.left]
    [LocallyOfFiniteType G.X.hom] (hG : HasTrivialUnipotentRadical G) (hs : IsClosedSubgroup s)
    (hc : IsCentral s) {N : Type} [Fintype N] [DecidableEq N] (ρ : MatrixRepresentation G N)
    [IsClosedImmersion ρ.hom.hom.left] {m : ℕ} (hm : m ≠ 0)
    (heig : ∀ y : rationalPoints S,
      ∀ c ∈ (ρ.rationalMatrix (y ≫ s.hom.hom) : Matrix N N K).charpoly.roots, c ^ m = 1) :
    ∃ x : S.X.left, IsClosed ({x} : Set S.X.left) ∧ IsOpen ({x} : Set S.X.left) := by
  have : IsClosedImmersion s.hom.hom.left := hs
  have : LocallyOfFiniteType S.X.hom := by
    rw [← Over.w s.hom.hom]
    infer_instance
  obtain ⟨H, f, hι, hsm, hconn, hopen, -⟩ := ReducedSubgroup.exists_reducedIdentityComponent s hs
  have : IsClosedImmersion (f ≫ s).hom.hom.left := hι
  have : Mono (f ≫ s).hom.hom := Over.mono_of_mono_left _
  have hcent : IsCentral (f ≫ s) := hc.comp f
  have hnormal : (SubgroupFunctor.range (f ≫ s)).IsNormal := by
    intro T g x _ hx
    obtain ⟨y, rfl⟩ := SubgroupFunctor.mem_range.1 hx
    rw [← (commute_of_mem_center (hcent T y) g).eq, mul_inv_cancel_right]
    exact SubgroupFunctor.mem_range.2 ⟨y, rfl⟩
  have hcomm : ∀ h h' : Over.mk (𝟙 (Spec (CommRingCat.of K))) ⟶ H.X, Commute h h' := by
    intro h h'
    change h * h' = h' * h
    refine (cancel_mono (f ≫ s).hom.hom).1 ?_
    rw [MonObj.mul_comp, MonObj.mul_comp]
    exact (commute_of_mem_center (hcent _ h) _).eq
  have : IsClosedImmersion (ρ.restrict (f ≫ s)).hom.hom.left := by
    change IsClosedImmersion ((f ≫ s).hom.hom.left ≫ ρ.hom.hom.left)
    infer_instance
  have : IsReduced H.X.left :=
    Langlands.AlgebraicGeometry.SmoothReducedProof.isReduced_of_smooth_over_field K H.X.left
      H.X.hom
  have : IsAffine H.X.left := isAffine_of_isAffineHom (f ≫ s).hom.hom.left
  have heig' : ∀ h : Over.mk (𝟙 (Spec (CommRingCat.of K))) ⟶ H.X,
      ∀ c ∈ ((ρ.restrict (f ≫ s)).rationalMatrix h : Matrix N N K).charpoly.roots,
        c ^ m = 1 := by
    intro h c hc'
    have hx : h ≫ (f ≫ s).hom.hom = (h ≫ f.hom.hom) ≫ s.hom.hom := by
      simp only [Category.assoc]
      rfl
    rw [MatrixRepresentation.rationalMatrix_restrict, hx] at hc'
    exact heig _ c hc'
  have hunip : IsUnipotent H := isUnipotent_of_eigenvalues (ρ.restrict (f ≫ s)) hcomm hm heig'
  have hbot := hG H (f ≫ s) hι hsm hconn hunip hnormal
  have hone : (𝟙 H.X : H.X ⟶ H.X) = 1 := by
    refine (cancel_mono (f ≫ s).hom.hom).1 ?_
    have h1 : 𝟙 H.X ≫ (f ≫ s).hom.hom ∈ (SubgroupFunctor.range (f ≫ s)).carrier H.X :=
      SubgroupFunctor.mem_range.2 ⟨_, rfl⟩
    rw [hbot, SubgroupFunctor.bot_carrier, Subgroup.mem_bot] at h1
    rw [h1, MonObj.one_comp]
  have hsub : Subsingleton H.X.left := by
    constructor
    intro a b
    have e : ∀ x : H.X.left, x = η[H.X].left ((toUnit H.X).left x) := fun x =>
      congrArg (fun φ : H.X ⟶ H.X => φ.left x) hone
    have hK : ∀ p q : (Spec (CommRingCat.of K) : Scheme), p = q := fun p q =>
      Subsingleton.elim p q
    rw [e a, e b, hK ((toUnit H.X).left a) ((toUnit H.X).left b)]
  set x₀ : S.X.left := η[S.X].left (IsLocalRing.closedPoint K) with hx₀
  have hrange : Set.range f.hom.hom.left = {x₀} := by
    have hf : f.hom.hom.left (η[H.X].left (IsLocalRing.closedPoint K)) = x₀ := by
      change (η[H.X] ≫ f.hom.hom).left _ = _
      rw [IsMonHom.one_hom]
    ext y
    constructor
    · rintro ⟨a, rfl⟩
      rw [Subsingleton.elim a (η[H.X].left (IsLocalRing.closedPoint K)), hf]
      rfl
    · rintro rfl
      exact ⟨_, hf⟩
  refine ⟨x₀, ?_, hrange ▸ hopen⟩
  exact (pointEquivClosedPoint S.X.hom ⟨η[S.X].left, Over.w η[S.X]⟩).2

/-- Under the same hypotheses, `S` has finitely many rational points. -/
theorem finite_rationalPoints_of_eigenvalues
    {G S : GroupScheme (Spec (CommRingCat.of K))} (s : S ⟶ G) [IsAffine G.X.left]
    [LocallyOfFiniteType G.X.hom] (hG : HasTrivialUnipotentRadical G) (hs : IsClosedSubgroup s)
    (hc : IsCentral s) {N : Type} [Fintype N] [DecidableEq N] (ρ : MatrixRepresentation G N)
    [IsClosedImmersion ρ.hom.hom.left] {m : ℕ} (hm : m ≠ 0)
    (heig : ∀ y : rationalPoints S,
      ∀ c ∈ (ρ.rationalMatrix (y ≫ s.hom.hom) : Matrix N N K).charpoly.roots, c ^ m = 1) :
    Finite (rationalPoints S) := by
  obtain ⟨x, hxc, hxo⟩ := exists_isClosed_isOpen_singleton_of_eigenvalues s hG hs hc ρ hm heig
  have : IsClosedImmersion s.hom.hom.left := hs
  have : LocallyOfFiniteType S.X.hom := by
    rw [← Over.w s.hom.hom]
    infer_instance
  have : IsAffine S.X.left := isAffine_of_isAffineHom s.hom.hom.left
  have : Finite S.X.left := finite_of_isOpen_singleton x hxc hxo
  exact Finite.of_equiv _ (rationalPointEquivClosedPoint S.X).symm

end Langlands.BruhatTits.RationalPoints.CentralNormKernel
