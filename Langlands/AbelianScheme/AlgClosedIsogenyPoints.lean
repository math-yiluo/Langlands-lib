import Langlands.AbelianScheme.AlgClosedIsogenyPointLifting
import Langlands.AlgebraicGeometry.FiniteEtale.GeometricFiberFiniteProof
import Mathlib.GroupTheory.QuotientGroup.Basic

/-! # Isogenies on points valued in an algebraically closed field -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

/-- A surjective homomorphism of commutative groups with finite kernel has a
quasi-inverse: for `N` the order of the kernel, both composites are `N`-th powers. -/
theorem exists_pow_quasiInverse {M M' : Type*} [CommGroup M] [CommGroup M']
    (φ : M →* M') (hsurj : Function.Surjective φ) (hfin : Finite φ.ker) :
    ∃ N : ℕ, 0 < N ∧ (∀ x ∈ φ.ker, x ^ N = 1) ∧
      ∃ ψ : M' →* M, (∀ y, φ (ψ y) = y ^ N) ∧ (∀ x, ψ (φ x) = x ^ N) := by
  let N := Nat.card φ.ker
  have hN : 0 < N := Nat.card_pos
  have hker : ∀ x ∈ φ.ker, x ^ N = 1 := by
    intro x hx
    have h : (⟨x, hx⟩ : φ.ker) ^ N = 1 := pow_card_eq_one'
    exact congrArg Subtype.val h
  have hle : φ.ker ≤ (powMonoidHom N : M →* M).ker := fun x hx => hker x hx
  let e := QuotientGroup.quotientKerEquivOfSurjective φ hsurj
  let ψ : M' →* M :=
    (QuotientGroup.lift φ.ker (powMonoidHom N) hle).comp e.symm.toMonoidHom
  have hψ : ∀ x, ψ (φ x) = x ^ N := by
    intro x
    have hx : e.symm (φ x) = (x : M ⧸ φ.ker) := by
      apply e.injective
      rw [MulEquiv.apply_symm_apply]
      rfl
    change QuotientGroup.lift φ.ker (powMonoidHom N) hle (e.symm (φ x)) = x ^ N
    rw [hx, QuotientGroup.lift_mk]
    rfl
  refine ⟨N, hN, hker, ψ, ?_, hψ⟩
  intro y
  obtain ⟨x, rfl⟩ := hsurj y
  rw [hψ, map_pow]

variable {S : Scheme.{u}} {G H : Grp (Over S)}

/-- The homomorphism of points induced by a group-scheme homomorphism. -/
abbrev pointsHom (f : G ⟶ H) (T : Over S) : (T ⟶ G.X) →* (T ⟶ H.X) :=
  IsMonHom.monoidHom f.hom.hom T

variable {K : Type u} [Field K] [IsAlgClosed K] (s : Spec (CommRingCat.of K) ⟶ S)

/-- An isogeny is surjective on points valued in an algebraically closed field. -/
theorem IsIsogeny.pointsHom_surjective {f : G ⟶ H} (hf : IsIsogeny f) :
    Function.Surjective (pointsHom f (Over.mk s)) := by
  have : IsFinite f.hom.hom.left := hf.1
  have : Surjective f.hom.hom.left := hf.2.2
  intro y
  obtain ⟨a, ha⟩ :=
    Langlands.exists_point_lift_of_locallyOfFiniteType_surjective f.hom.hom.left y.left
  refine ⟨Over.homMk a ?_, ?_⟩
  · rw [← Over.w f.hom.hom, ← Category.assoc, ha]
    exact Over.w y
  · exact Over.OverMorphism.ext ha

omit [IsAlgClosed K] in
/-- An isogeny has only finitely many kernel points valued in a field. -/
theorem IsIsogeny.finite_ker_pointsHom {f : G ⟶ H} (hf : IsIsogeny f) :
    Finite (pointsHom f (Over.mk s)).ker := by
  have : IsFinite f.hom.hom.left := hf.1
  let e : Spec (CommRingCat.of K) ⟶ H.X.left := (1 : Over.mk s ⟶ H.X).left
  have := Langlands.AlgebraicGeometry.FiniteEtale.finite_sections_of_isFinite
    (pullback.snd f.hom.hom.left e)
  have hk : ∀ x : (pointsHom f (Over.mk s)).ker,
      x.val.left ≫ f.hom.hom.left = 𝟙 _ ≫ e := by
    intro x
    rw [Category.id_comp]
    exact congrArg (fun z => z.left) (MonoidHom.mem_ker.mp x.property)
  refine Finite.of_injective
    (fun x : (pointsHom f (Over.mk s)).ker =>
      (⟨pullback.lift x.val.left (𝟙 _) (hk x), pullback.lift_snd _ _ _⟩ :
        {z : Spec (CommRingCat.of K) ⟶ pullback f.hom.hom.left e //
          z ≫ pullback.snd f.hom.hom.left e = 𝟙 _})) ?_
  intro x y hxy
  have h := congrArg (fun z => z.val ≫ pullback.fst f.hom.hom.left e) hxy
  simp only [pullback.lift_fst] at h
  exact Subtype.ext (Over.OverMorphism.ext h)

/-- Points of an isogeny valued in an algebraically closed field admit a
quasi-inverse homomorphism whose composites are a positive power. -/
theorem IsIsogeny.exists_points_quasiInverse [IsCommMonObj G.X] [IsCommMonObj H.X]
    {f : G ⟶ H} (hf : IsIsogeny f) :
    ∃ N : ℕ, 0 < N ∧ (∀ x : Over.mk s ⟶ G.X, x ≫ f.hom.hom = 1 → x ^ N = 1) ∧
      ∃ ψ : (Over.mk s ⟶ H.X) →* (Over.mk s ⟶ G.X), ∀ y, ψ y ≫ f.hom.hom = y ^ N := by
  obtain ⟨N, hN, hker, ψ, hψ, -⟩ := exists_pow_quasiInverse (pointsHom f (Over.mk s))
    (hf.pointsHom_surjective s) (hf.finite_ker_pointsHom s)
  exact ⟨N, hN, fun x hx => hker x (MonoidHom.mem_ker.mpr hx), ψ, hψ⟩

end Langlands.GroupScheme
