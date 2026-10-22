import Langlands.WeilDeligne.Basic
import Langlands.Weil.Representation.Twist

/-! # Character twists of Weil–Deligne pairs -/

noncomputable section

universe uK uG uV uW

open CategoryTheory

namespace Langlands.WeilDeligneRepresentation

variable {K : Type uK} {G : Type uG} [Field K] [Group G] {ν : G →* Kˣ}

/-- A scalar twist changes the Weil action and keeps the same monodromy. -/
def twist (χ : G →* Kˣ) (A : WeilDeligneRepresentation.{uK, uG, uV} K G ν) :
    WeilDeligneRepresentation.{uK, uG, uV} K G ν where
  toFiniteRepresentation := FiniteRepresentation.twist χ A.toFiniteRepresentation
  monodromy := A.monodromy
  nilpotent := A.nilpotent
  covariance g := by
    ext v
    change (χ g : K) • A.representation g
      (A.monodromy ((χ g⁻¹ : K) • A.representation g⁻¹ v)) =
        (ν g : K) • A.monodromy v
    rw [map_smul, map_smul, smul_smul]
    have hχ : (χ g : K) * (χ g⁻¹ : K) = 1 := by
      rw [← Units.val_mul, ← map_mul, mul_inv_cancel, map_one, Units.val_one]
    rw [hχ, one_smul]
    exact LinearMap.congr_fun (A.covariance g) v

/-- Twisting a morphism retains its linear map and monodromy square. -/
def twistMap (χ : G →* Kˣ) {A : WeilDeligneRepresentation.{uK, uG, uV} K G ν}
    {B : WeilDeligneRepresentation.{uK, uG, uW} K G ν} (f : Hom A B) :
    Hom (twist χ A) (twist χ B) :=
  ⟨Langlands.twistIntertwining χ f.intertwiner, f.comm_monodromy⟩

/-- Cancellation of the common character also preserves the monodromy square. -/
def untwistMap (χ : G →* Kˣ) {A : WeilDeligneRepresentation.{uK, uG, uV} K G ν}
    {B : WeilDeligneRepresentation.{uK, uG, uW} K G ν}
    (f : Hom (twist χ A) (twist χ B)) : Hom A B :=
  ⟨Langlands.untwistIntertwining χ f.intertwiner, f.comm_monodromy⟩

/-- Twisting is a functor on the category of pairs with a fixed norm character. -/
def twistFunctor (χ : G →* Kˣ) : WeilDeligneRepresentation.{uK, uG, uV} K G ν ⥤
    WeilDeligneRepresentation.{uK, uG, uV} K G ν where
  obj := twist χ
  map f := twistMap χ f
  map_id _ := by apply Hom.ext; rfl
  map_comp _ _ := by apply Hom.ext; rfl

/-- The pair twist functor is fully faithful. -/
def twistFullyFaithful (χ : G →* Kˣ) : (twistFunctor.{uK, uG, uV} (ν := ν) χ).FullyFaithful where
  preimage f := untwistMap χ f
  map_preimage _ := by apply Hom.ext; rfl
  preimage_map _ := by apply Hom.ext; rfl

/-- Twisting preserves genuine pair equivalences on their original carriers. -/
def twistEquiv (χ : G →* Kˣ) {A : WeilDeligneRepresentation.{uK, uG, uV} K G ν}
    {B : WeilDeligneRepresentation.{uK, uG, uW} K G ν} (e : Equiv A B) :
    Equiv (twist χ A) (twist χ B) :=
  ⟨Langlands.twistEquiv χ e.representationEquiv, e.comm_monodromy⟩

/-- Character twisting descends to genuine pair isomorphism classes. -/
def twistClass (χ : G →* Kˣ) : IsomorphismClasses.{uK, uG, uV} K G ν →
    IsomorphismClasses.{uK, uG, uV} K G ν :=
  Quotient.map (twist χ) (fun _ _ ⟨e⟩ => ⟨twistEquiv χ e⟩)

end Langlands.WeilDeligneRepresentation
