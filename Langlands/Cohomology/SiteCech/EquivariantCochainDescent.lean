import Langlands.Cohomology.SiteCech.InjectiveCoefficients

/-! # Descent of primitives from exact equivariant three-term models -/

noncomputable section

namespace Langlands.Cohomology.SiteCech

open CategoryTheory CategoryTheory.Limits

universe u v uE vE

variable {D : Type u} [Category.{v} D] [Preadditive D]
variable {E : Type uE} [Category.{vE} E] [Abelian E]
variable (V : E ⥤ D) [V.Faithful] [V.PreservesZeroMorphisms]
variable (P : ChainComplex D ℕ) (I : E) (F : D) (e : V.obj I ≅ F)

/-- An exact equivariant model of three consecutive terms, together with an
equivariant lift of one ordinary cochain. Both differential squares are part
of the data. No isomorphism in the upper degree is needed. -/
structure EquivariantCochainLift (n : ℕ) (x : P.X (n + 1) ⟶ F) where
  complex : ShortComplex E
  exact : complex.Exact
  lowerIso : V.obj complex.X₃ ≅ P.X n
  middleIso : V.obj complex.X₂ ≅ P.X (n + 1)
  upperMap : V.obj complex.X₁ ⟶ P.X (n + 2)
  upper_square : V.map complex.f ≫ middleIso.hom =
    upperMap ≫ P.d (n + 2) (n + 1)
  lower_square : V.map complex.g ≫ lowerIso.hom =
    middleIso.hom ≫ P.d (n + 1) n
  lift : complex.X₂ ⟶ I
  lift_eq : V.map lift ≫ e.hom = middleIso.hom ≫ x

variable {V P I F e}

/-- Faithfulness and the upper differential square turn the lifted ordinary
cocycle into a cocycle in the equivariant category. -/
theorem EquivariantCochainLift.cocycle {n : ℕ} {x : P.X (n + 1) ⟶ F}
    (L : EquivariantCochainLift V P I F e n x)
    (hx : P.d (n + 2) (n + 1) ≫ x = 0) :
    L.complex.f ≫ L.lift = 0 := by
  apply V.map_injective
  apply (cancel_mono e.hom).1
  rw [Functor.map_comp, Category.assoc, L.lift_eq, ← Category.assoc,
    L.upper_square, Category.assoc, hx, comp_zero, Functor.map_zero, zero_comp]

/-- The ordinary primitive obtained by injective extension in the exact model
and the lower-term comparison. -/
def EquivariantCochainLift.primitive [Injective I]
    {n : ℕ} {x : P.X (n + 1) ⟶ F}
    (L : EquivariantCochainLift V P I F e n x)
    (hx : P.d (n + 2) (n + 1) ≫ x = 0) : P.X n ⟶ F :=
  L.lowerIso.inv ≫
    V.map (L.exact.descToInjective L.lift (L.cocycle hx)) ≫ e.hom

/-- The lower differential square identifies the constructed primitive's
differential with the original cochain. -/
theorem EquivariantCochainLift.comp_primitive [Injective I]
    {n : ℕ} {x : P.X (n + 1) ⟶ F}
    (L : EquivariantCochainLift V P I F e n x)
    (hx : P.d (n + 2) (n + 1) ≫ x = 0) :
    P.d (n + 1) n ≫ L.primitive hx = x := by
  let y := L.exact.descToInjective L.lift (L.cocycle hx)
  have hy : L.complex.g ≫ y = L.lift :=
    L.exact.comp_descToInjective L.lift (L.cocycle hx)
  change P.d (n + 1) n ≫ (L.lowerIso.inv ≫ V.map y ≫ e.hom) = x
  apply (cancel_epi L.middleIso.hom).1
  calc
    L.middleIso.hom ≫ P.d (n + 1) n ≫ L.lowerIso.inv ≫ V.map y ≫ e.hom =
        V.map L.complex.g ≫ V.map y ≫ e.hom := by
      rw [← Category.assoc L.middleIso.hom (P.d (n + 1) n) _,
        ← L.lower_square, Category.assoc, L.lowerIso.hom_inv_id_assoc]
    _ = V.map L.lift ≫ e.hom := by
      rw [← Category.assoc, ← Functor.map_comp, hy]
    _ = L.middleIso.hom ≫ x := L.lift_eq

/-- A cocycle with an exact equivariant model has an ordinary primitive
whenever the equivariant coefficient is injective. -/
theorem EquivariantCochainLift.exists_primitive [Injective I]
    {n : ℕ} {x : P.X (n + 1) ⟶ F}
    (L : EquivariantCochainLift V P I F e n x)
    (hx : P.d (n + 2) (n + 1) ≫ x = 0) :
    ∃ y : P.X n ⟶ F, P.d (n + 1) n ≫ y = x :=
  ⟨L.primitive hx, L.comp_primitive hx⟩

end Langlands.Cohomology.SiteCech
