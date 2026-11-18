import Langlands.GroupScheme.ArtinianUniformExponent
import Langlands.GroupScheme.UniformExponentApproximation
import Langlands.AlgebraicGeometry.QuasiFiniteArtinianExhaustionStatement
import Mathlib.Data.Nat.Factorial.Basic

/-! # Reduction of uniform exponents to Artinian bases and subscheme exhaustion -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1000000

namespace Langlands.GroupScheme.UniformExponentReduction

variable {S : Scheme.{u}} (G : GroupScheme S) [IsCommMonObj G.X]

private abbrev powerMap (n : ℕ) : G.X.left ⟶ G.X.left :=
  (multiplication G (n : ℤ)).hom.hom.left

private abbrev unitMap : G.X.left ⟶ G.X.left :=
  (1 : G ⟶ G).hom.hom.left

private theorem powerMap_comp_iff {T : Over S} (x : T ⟶ G.X) (n : ℕ) :
    x.left ≫ powerMap G n = x.left ≫ unitMap G ↔ x ^ n = 1 := by
  constructor
  · intro he
    have he' : x ≫ (multiplication G (n : ℤ)).hom.hom =
        x ≫ (1 : G ⟶ G).hom.hom :=
      Over.OverMorphism.ext he
    simpa only [points_multiplication, zpow_natCast, Grp.Hom.hom_one,
      Mon.Hom.hom_one, MonObj.comp_one] using he'
  · intro hp
    have he' : x ≫ (multiplication G (n : ℤ)).hom.hom =
        x ≫ (1 : G ⟶ G).hom.hom := by
      simpa only [points_multiplication, zpow_natCast, Grp.Hom.hom_one,
        Mon.Hom.hom_one, MonObj.comp_one] using hp
    exact congrArg (fun a => a.left) he'

private abbrev torsionScheme (i : ℕ) : Scheme.{u} :=
  equalizer (powerMap G i.factorial) (unitMap G)

private abbrev torsionι (i : ℕ) : torsionScheme G i ⟶ G.X.left :=
  equalizer.ι (powerMap G i.factorial) (unitMap G)

private theorem torsion_increasing (i k : ℕ) (hik : i ≤ k) :
    ∃ a : torsionScheme G i ⟶ torsionScheme G k, a ≫ torsionι G k = torsionι G i := by
  let x : Over.mk (torsionι G i ≫ G.X.hom) ⟶ G.X :=
    Over.homMk (torsionι G i) rfl
  have hx : x ^ i.factorial = 1 :=
    (powerMap_comp_iff G x _).mp (equalizer.condition _ _)
  have hk : x ^ k.factorial = 1 := by
    obtain ⟨r, hr⟩ := Nat.factorial_dvd_factorial hik
    rw [hr, pow_mul, hx, one_pow]
  exact ⟨equalizer.lift (torsionι G i) ((powerMap_comp_iff G x _).mpr hk),
    equalizer.lift_ι _ _⟩

private theorem isIso_pullback_equalizer {C : Type*} [Category C] [HasPullbacks C]
    {X Y T : C} (f g : X ⟶ Y) [HasEqualizer f g]
    (p : T ⟶ X) (hp : p ≫ f = p ≫ g) :
    IsIso (pullback.snd (equalizer.ι f g) p) := by
  have : IsSplitEpi (pullback.snd (equalizer.ι f g) p) :=
    IsSplitEpi.mk' ⟨pullback.lift (equalizer.lift p hp) (𝟙 T) (by simp),
      pullback.lift_snd _ _ _⟩
  exact isIso_of_mono_of_isSplitEpi _

/-- Artinian-local exponents, together with the geometric subscheme
exhaustion theorem, give the noetherian affine exponent assertion. -/
theorem noetherian_of_artinian_exhaustion
    (hArt : ArtinianUniformExponent.Statement.{u})
    (hEx : Langlands.AlgebraicGeometry.QuasiFiniteArtinianExhaustionStatement.{u, 0}) :
    UniformExponentApproximation.NoetherianAffineStatement.{u} := by
  intro R _ _ G hcomm hfp hqc hqs hqf
  let := hcomm
  let := hfp
  let := hqc
  let := hqs
  let := hqf
  obtain ⟨i, hi⟩ := hEx _ _ G.X.hom inferInstance hqf hqc ℕ (torsionScheme G) (torsionι G)
    (fun _ => inferInstance) (torsion_increasing G) (by
      intro A _ _ _ b
      let H := (baseChange b).obj G
      have hcommH : IsCommMonObj H.X := baseChange_isCommMonObj b G
      have hqcH : QuasiCompact H.X.hom := by
        change QuasiCompact (pullback.snd G.X.hom b)
        infer_instance
      have hqfH : LocallyQuasiFinite H.X.hom := by
        change LocallyQuasiFinite (pullback.snd G.X.hom b)
        infer_instance
      obtain ⟨m, hm, hpow⟩ := hArt A H hqcH hqfH
      let V := H.X
      let x := baseChangePointsEquiv b G V (𝟙 V)
      have hx : x ^ m.factorial = 1 := by
        have hp := UniformExponentLocality.points_pow_of_dvd H hpow
          (Nat.dvd_factorial hm (le_refl m)) V (𝟙 V)
        have hp' := congrArg (baseChangePointsEquiv b G V) hp
        simpa only [map_pow, map_one] using hp'
      have he := (powerMap_comp_iff G x m.factorial).mpr hx
      have he' : pullback.fst G.X.hom b ≫ powerMap G m.factorial =
          pullback.fst G.X.hom b ≫ unitMap G := by
        simpa only [x, baseChangePointsEquiv_left, V, Over.id_left,
          Category.id_comp] using he
      exact ⟨m, isIso_pullback_equalizer _ _ _ he'⟩)
  have := hi
  have he : powerMap G i.factorial = unitMap G :=
    (cancel_epi (torsionι G i)).mp (equalizer.condition _ _)
  have he' : multiplication G (i.factorial : ℤ) = (1 : G ⟶ G) := by
    apply Grp.hom_ext
    exact Over.OverMorphism.ext he
  exact ⟨i.factorial, Nat.factorial_pos i,
    (UniformExponentLocality.points_pow_iff G i.factorial).mpr he'⟩

/-- The two remaining geometric and Artinian inputs to the unchanged target. -/
def Statement : Prop :=
  ArtinianUniformExponent.Statement.{u} →
    Langlands.AlgebraicGeometry.QuasiFiniteArtinianExhaustionStatement.{u, 0} →
      QuasiFiniteCommutativeUniformExponentStatement.{u}

/-- Complete assembly of the arbitrary-base reduction from its two inputs. -/
theorem reduction : Statement.{u} := by
  intro hArt hEx
  exact UniformExponentApproximation.uniformExponent_of_noetherian
    (noetherian_of_artinian_exhaustion hArt hEx)

end Langlands.GroupScheme.UniformExponentReduction
