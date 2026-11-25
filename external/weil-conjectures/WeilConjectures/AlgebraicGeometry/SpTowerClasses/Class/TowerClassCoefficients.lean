/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SpTowerClasses.Class.TowerClassReduction

/-! # Coefficients for canonical tower classes

Source: blueprint main-20261015, chap-Smooth-purity,
`sk-prop-sp-tower-geometric-classes` (blueprint: def-sp-tower-class-coefficients).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genSizeOf false
set_option genInjectivity false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall

universe u u₁ v₁ u₂ v₂ w₁ w₂ w₃

open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme WeilConjectures

namespace AlgebraicGeometry.ProEtale.SpTowerClasses

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

/-- Positive finite integral coefficient rings. Source: classes (2)
(blueprint: def-sp-tower-class-coefficients). -/
abbrev Rlevel (T : Scheme.{u}) (n : ℕ) :
    Sheaf (Scheme.ProEt.topology T) CommRingCat.{u + 1} :=
  (constantSheaf.{u, u + 1, u + 1, u + 2} (Scheme.ProEt.topology T) CommRingCat.{u + 1}).obj
    (CommRingCat.of (ULift.{u + 1, 0} (ZMod (l ^ (n + 1)))))

/-- Actual quotient transitions on Z/ell^n. Source: classes (2)
(blueprint: def-sp-tower-class-coefficients). -/
def Rtransition (T : Scheme.{u}) (n : ℕ) : Rlevel l T (n + 1) ⟶ Rlevel l T n :=
  (constantSheaf.{u, u + 1, u + 1, u + 2} (Scheme.ProEt.topology T) CommRingCat.{u + 1}).map
    (CommRingCat.ofHom (ULift.ringEquiv.{0, u + 1}.symm.toRingHom.comp
      ((ZMod.castHom (pow_dvd_pow l (Nat.le_succ (n + 1))) (ZMod (l ^ (n + 1)))).comp
        ULift.ringEquiv.{0, u + 1}.toRingHom)))

/-- The coefficient ring tower R. Source: classes (2)
(blueprint: def-sp-tower-class-coefficients). -/
def Rrings (T : Scheme.{u}) := Functor.ofOpSequence (Rtransition l T)

/-- The coefficient ring tower A is the published one.
Source: classes (2) (blueprint: def-sp-tower-class-coefficients). -/
abbrev Arings (T : Scheme.{u}) := spCoefficientCommRings l E T

/-- The quotient kills the required positive ell power.
Source: classes (2), coefficient convention (blueprint: def-sp-tower-class-coefficients).
Proof: the ell power belongs to the (n+1)-st power of the principal ideal (ell).
Its image in that quotient is zero, including the zero coefficient ring. -/
theorem coefficient_annihilates (n : ℕ) :
    ((l ^ (n + 1) : ℕ) : SpTowerShriek.R l E n) = 0 := by
  have h := Ideal.pow_mem_pow
    (Ideal.mem_span_singleton_self (l : Padic.coefficientExtensionIntegers l E)) (n + 1)
  simpa only [map_pow, map_natCast, Nat.cast_pow] using
    (Ideal.Quotient.eq_zero_iff_mem.mpr h)

/-- The unique unital quotient map of the actual finite rings.
Source: classes (2) (blueprint: def-sp-tower-class-coefficients). -/
def coefficientMap (T : Scheme.{u}) (n : ℕ) :
    Rlevel l T n ⟶ (Arings l E T).obj (op n) :=
  (constantSheaf.{u, u + 1, u + 1, u + 2} (Scheme.ProEt.topology T) CommRingCat.{u + 1}).map
    (CommRingCat.ofHom (ULift.ringEquiv.{u, u + 1}.symm.toRingHom.comp
      ((ZMod.castHom (ringChar.dvd (coefficient_annihilates l E n))
        (SpTowerShriek.R l E n)).comp ULift.ringEquiv.{0, u + 1}.toRingHom)))

/-- The coefficient maps commute with the specified quotient transitions.
Source: classes (2), proof step 8 (blueprint: def-sp-tower-class-coefficients).
Proof: both maps are induced by the integer-ring quotient and take one to one.
They agree on integers, hence on Z/ell^(n+2), and constant sheafification preserves
this equality. -/
theorem coefficientMap_transition (T : Scheme.{u}) (n : ℕ) :
    coefficientMap l E T (n + 1) ≫ SpTowerShriek.tau l E T n =
      (Rrings l T).map (homOfLE (Nat.le_succ n)).op ≫ coefficientMap l E T n := by
  simp only [coefficientMap, SpTowerShriek.tau, Arings, spCoefficientCommRings,
    Rrings, Functor.ofOpSequence_map_homOfLE_succ, Rtransition, ← Functor.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  apply (RingHom.cancel_right
    (f := (ULift.ringEquiv.{0, u + 1} (R := ZMod (l ^ (n + 1 + 1)))).symm.toRingHom)
    (fun x ↦ ⟨x.down, rfl⟩)).mp
  exact Subsingleton.elim _ _

/-- The canonical map of ring objects on the inverse-system topos.
Source: classes (2) (blueprint: def-sp-tower-class-coefficients). -/
def coefficientSystemMap (T : Scheme.{u}) :=
  SemilinearSections.systemMap.{u + 1, u, u + 1} (Scheme.ProEt.topology T)
    (fun n ↦ (Rrings l T).obj (op n))
    (fun n ↦ (Rrings l T).map (homOfLE (Nat.le_succ n)).op)
    (SpTowerShriek.B l E T) (SpTowerShriek.tau l E T)
    (coefficientMap l E T) (coefficientMap_transition l E T)

/-- The unit under actual coefficient restriction is induced by the ring map.
Source: classes (2), proof step 8 (blueprint: def-sp-tower-class-coefficients).
Proof: at every section the formula is the unital ring homomorphism from the
coefficient system map. It is linear for restriction of scalars, commutes with
all presheaf maps and is uniquely determined by that formula. -/
theorem scalarGenerator_existsUnique (T : Scheme.{u}) :
    ∃! f : coefficient T (Rrings l T) ⟶
      (SemilinearSections.res.{u + 1, u, u + 1}
        (coefficientSystemMap l E T)).obj (coefficient T (Arings l E T)),
      ∀ (U : (ℕ × T.ProEt)ᵒᵖ)
        (x : (coefficient T (Rrings l T)).val.obj U),
        HEq (f.val.app U x) ((coefficientSystemMap l E T).hom.app U x) := by
  let φ := (sheafCompose (coefficientSequenceTopology (Scheme.ProEt.topology T))
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map (coefficientSystemMap l E T)
  let f : coefficient T (Rrings l T) ⟶
      (SemilinearSections.res.{u + 1, u, u + 1}
        (coefficientSystemMap l E T)).obj (coefficient T (Arings l E T)) :=
    { val :=
      { app := fun U ↦ ModuleCat.homMk
          ((forget₂ RingCat AddCommGrpCat).map (φ.hom.app U)) (fun r ↦ by
            ext x
            exact ((φ.hom.app U).hom.map_mul r x).symm)
        naturality := fun {U V} g ↦ by
          apply ModuleCat.hom_ext
          apply LinearMap.ext
          intro x
          exact ConcreteCategory.congr_hom (φ.hom.naturality g) x } }
  refine ⟨f, fun _ _ ↦ HEq.rfl, ?_⟩
  intro g hg
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro U
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  exact eq_of_heq (hg U x)

/-- The canonical map between coefficient units before deriving scalar extension.
Source: classes (2) (blueprint: def-sp-tower-class-coefficients). -/
def scalarGenerator (T : Scheme.{u}) :=
  (scalarGenerator_existsUnique l E T).exists.choose

end AlgebraicGeometry.ProEtale.SpTowerClasses

attribute [instance high] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
