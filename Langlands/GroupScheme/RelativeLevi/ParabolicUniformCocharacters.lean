import Langlands.GroupScheme.RelativeLevi.ParabolicFibreLatticeComparison
import Langlands.GroupScheme.Rational.GenericCocharacter
import Langlands.GroupScheme.Rational.StandardCocharacterProof
import Langlands.GroupScheme.Torus.FieldPointMaximality
import Langlands.GroupScheme.Torus.MaximalSplitComparison
import Langlands.GroupScheme.Reductive.BaseChange
import Mathlib.Data.Set.Finite.Powerset

/-! # One finite exponent family of standard cocharacters on every field fibre -/

noncomputable section

universe u v

open CategoryTheory AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 200000

namespace Langlands.GroupScheme

variable {R : Type u} [CommRing R] (I : Type u) [Fintype I]
  (G : GroupScheme (Spec (CommRingCat.of R))) [IsAffineHom G.X.hom]
  (i : splitTorus (Spec (CommRingCat.of R)) I ⟶ G)
  {J : Type v} (P : RootDatum J (I → ℤ) (I → ℤ))

local instance uniformCocharacterAffine {k : Type u} [Field k] [Algebra R k] :
    IsAffineHom ((baseChange (algebraBaseMap R k)).obj G).X.hom :=
  inferInstanceAs (IsAffineHom (Limits.pullback.snd G.X.hom (algebraBaseMap R k)))

/-- A single finite family of integer exponent vectors becomes the complete
family of standard cocharacters on every supplied field fibre. A reference
field fibre is used only to choose the family. -/
theorem exists_uniform_standardCocharacters
    (hG : IsReductive G)
    (hi : IsFibrewiseMaximalTorus (T := splitTorus.commGroupScheme _ I) i)
    (hP : IsFibrewiseRootDatumOf I G i P)
    (k₀ : Type u) [Field k₀] [Algebra R k₀] :
    ∃ (A : Type u) (_ : Fintype A) (w : A → I → ℤ),
      ∀ (k : Type u) [Field k] [Algebra R k],
        ∃ ν : cocharacterLattice (splitTorus.commGroupScheme (Spec (CommRingCat.of k)) I),
          IsGenericCocharacter (splitTorus.baseChangeHom (K := k) G I i) ν ∧
          ∃ e : A ≃ {B : Set (characterLattice
              (splitTorus.commGroupScheme (Spec (CommRingCat.of k)) I)) //
            B ⊆ simpleRelativeRoots (splitTorus.baseChangeHom (K := k) G I i) ν},
            ∀ a, IsStandardCocharacter (splitTorus.baseChangeHom (K := k) G I i) ν
              (e a).1 (splitTorus.exponentCocharacter (Spec (CommRingCat.of k)) I (w a)) := by
  classical
  let : Smooth G.X.hom := hG.smooth
  let G₀ := (baseChange (algebraBaseMap R k₀)).obj G
  have hG₀ : IsConnectedReductive G₀ := hG.isConnectedReductive_baseChange _
  let : Smooth G₀.X.hom := hG₀.smooth
  let i₀ := splitTorus.baseChangeHom (K := k₀) G I i
  have hi₀ : IsMaximalSplitTorus
      (T := splitTorus.commGroupScheme (Spec (CommRingCat.of k₀)) I) i₀ :=
    (splitTorus.isMaximalTorus_baseChangeHom_of_fibrewise I G i hi k₀).isMaximalSplitTorus
      (isSplitTorus_splitTorus (S := Spec (CommRingCat.of k₀)) I)
  obtain ⟨ν₀, hν₀⟩ := IsSplitTorus.exists_genericCocharacter
    (T := splitTorus.commGroupScheme (Spec (CommRingCat.of k₀)) I) (G := G₀)
    hi₀.isSplitSubtorus.1 i₀
  let A := {B : Set (characterLattice
    (splitTorus.commGroupScheme (Spec (CommRingCat.of k₀)) I)) //
    B ⊆ simpleRelativeRoots
      (T := splitTorus.commGroupScheme (Spec (CommRingCat.of k₀)) I) i₀ ν₀}
  let : Fintype A :=
    (IsSplitTorus.finite_simpleRelativeRoots
      (T := splitTorus.commGroupScheme (Spec (CommRingCat.of k₀)) I) (G := G₀)
      i₀ hi₀.isSplitSubtorus.1 ν₀).finite_subsets.fintype
  have hex : ∀ a : A, ∃ ζ, IsStandardCocharacter
      (T := splitTorus.commGroupScheme (Spec (CommRingCat.of k₀)) I) i₀ ν₀ a.1 ζ :=
    fun a => (standardCocharacter k₀ G₀ hG₀
      (splitTorus.commGroupScheme (Spec (CommRingCat.of k₀)) I)
      i₀ hi₀ ν₀ hν₀ a.1 a.2).1
  choose ζ hζ using hex
  let w : A → I → ℤ := fun a => splitTorus.cocharacterLatticeEquiv k₀ I (ζ a)
  have hw (a : A) :
      splitTorus.exponentCocharacter (Spec (CommRingCat.of k₀)) I (w a) = ζ a := by
    simp only [w, splitTorus.exponentCocharacter_eq_cocharacterLatticeEquiv_symm,
      AddEquiv.symm_apply_apply]
  refine ⟨A, inferInstance, w, fun k _ _ => ?_⟩
  let d := fibreParabolicRootLatticeComparison I G i P hP k₀ k
  refine ⟨d.cocharacterEquiv ν₀, (d.generic_iff ν₀).mpr hν₀,
    d.faceEquiv ν₀, fun a => ?_⟩
  have h := (d.standard_iff ν₀ (ζ a) a).mpr (hζ a)
  have heq : d.cocharacterEquiv (ζ a) =
      splitTorus.exponentCocharacter (Spec (CommRingCat.of k)) I (w a) := by
    rw [← hw a]
    exact fibreParabolicRootLatticeComparison_cocharacter I G i P hP k₀ k (w a)
  rwa [heq] at h

/-- Fixed integer vectors, with a complete standard-face interpretation on
all field algebras of the base ring. -/
structure UniformStandardCocharacterFamily where
  Index : Type u
  fintypeIndex : Fintype Index
  exponents : Index → I → ℤ
  standard : ∀ (k : Type u) [Field k] [Algebra R k],
    ∃ ν : cocharacterLattice (splitTorus.commGroupScheme (Spec (CommRingCat.of k)) I),
      IsGenericCocharacter (splitTorus.baseChangeHom (K := k) G I i) ν ∧
      ∃ e : Index ≃ {B : Set (characterLattice
          (splitTorus.commGroupScheme (Spec (CommRingCat.of k)) I)) //
        B ⊆ simpleRelativeRoots (splitTorus.baseChangeHom (K := k) G I i) ν},
        ∀ a, IsStandardCocharacter (splitTorus.baseChangeHom (K := k) G I i) ν
          (e a).1 (splitTorus.exponentCocharacter (Spec (CommRingCat.of k)) I (exponents a))

attribute [instance] UniformStandardCocharacterFamily.fintypeIndex

/-- Choose one complete finite family, using a reference field only for its
construction; the resulting specification applies to every field algebra. -/
def uniformStandardCocharacterFamily
    (hG : IsReductive G)
    (hi : IsFibrewiseMaximalTorus (T := splitTorus.commGroupScheme _ I) i)
    (hP : IsFibrewiseRootDatumOf I G i P)
    (k₀ : Type u) [Field k₀] [Algebra R k₀] :
    UniformStandardCocharacterFamily I G i :=
  Classical.choice (show Nonempty (UniformStandardCocharacterFamily I G i) from by
    obtain ⟨A, hA, w, hw⟩ := exists_uniform_standardCocharacters I G i P hG hi hP k₀
    exact ⟨⟨A, hA, w, hw⟩⟩)

end Langlands.GroupScheme
