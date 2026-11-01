import Langlands.Global.AdelicBlockParabolic

/-!
# Unipotent radicals over actual number-field adeles

Restrict the actual parabolic splitting to the kernel of diagonal-block
projection and compare actual Levi conjugation and factorization.
-/

noncomputable section

universe uF

namespace Langlands.Global.AdelicBlockUnipotent

open NumberField IsDedekindDomain
open Langlands.GeneralLinear

variable (F : Type uF) [Field F] [NumberField F] {n : ℕ} (B : BlockShape n)

/-- Rational points of the actual block upper unipotent radical. -/
abbrev Rational := ↥(B.unipotentRadical F)

/-- The actual full adelic radical, with its inherited subgroup topology. -/
abbrev Full := ↥(B.unipotentRadical (AdeleRing (𝓞 F) F))

/-- The actual finite adelic radical, over the restricted-product ring. -/
abbrev Finite := ↥(B.unipotentRadical (FiniteAdeleRing (𝓞 F) F))

/-- The actual radical over the product of archimedean completions. -/
abbrev Infinite := ↥(B.unipotentRadical (InfiniteAdeleRing F))

/-- Restrict the rational diagonal map to the actual radical. -/
def rational : Rational F B →* Full F B where
  toFun u := ⟨AdelicBlockParabolic.rational F B u.val, by
    apply (B.mem_unipotentRadical_iff _ _).mpr
    intro i a b
    change algebraMap F (AdeleRing (𝓞 F) F)
      (u.val.val (B.index i a) (B.index i b)) = if a = b then 1 else 0
    rw [(B.mem_unipotentRadical_iff F u.val).mp u.property i a b]
    split_ifs <;> simp⟩
  map_one' := Subtype.ext (map_one _)
  map_mul' u v := Subtype.ext (map_mul _ u.val v.val)

@[simp] theorem rational_val (u : Rational F B) :
    (rational F B u).val = AdelicBlockParabolic.rational F B u.val := rfl

theorem rational_injective : Function.Injective (rational F B) := by
  intro u v h
  apply Subtype.ext
  exact AdelicBlockParabolic.rational_injective F B (congrArg Subtype.val h)

private def infiniteHom : Full F B →* Infinite F B where
  toFun u := ⟨AdelicBlockParabolic.infinite F B u.val, by
    change B.leviProjection (InfiniteAdeleRing F) (AdelicBlockParabolic.infinite F B u.val) = 1
    rw [AdelicBlockParabolic.leviProjection_infinite, u.property, map_one]⟩
  map_one' := Subtype.ext (map_one _)
  map_mul' u v := Subtype.ext (map_mul _ u.val v.val)

private def finiteHom : Full F B →* Finite F B where
  toFun u := ⟨AdelicBlockParabolic.finite F B u.val, by
    change B.leviProjection (FiniteAdeleRing (𝓞 F) F) (AdelicBlockParabolic.finite F B u.val) = 1
    rw [AdelicBlockParabolic.leviProjection_finite, u.property, map_one]⟩
  map_one' := Subtype.ext (map_one _)
  map_mul' u v := Subtype.ext (map_mul _ u.val v.val)

/-- Actual archimedean coefficient projection preserves the radical kernel. -/
def infinite : Full F B →ₜ* Infinite F B where
  toMonoidHom := infiniteHom F B
  continuous_toFun := ((AdelicBlockParabolic.infinite F B).continuous.comp continuous_subtype_val).subtype_mk _

/-- Actual finite coefficient projection preserves the radical kernel. -/
def finite : Full F B →ₜ* Finite F B where
  toMonoidHom := finiteHom F B
  continuous_toFun := ((AdelicBlockParabolic.finite F B).continuous.comp continuous_subtype_val).subtype_mk _

@[simp] theorem infinite_val (u : Full F B) :
    (infinite F B u).val = AdelicBlockParabolic.infinite F B u.val := rfl

@[simp] theorem finite_val (u : Full F B) :
    (finite F B u).val = AdelicBlockParabolic.finite F B u.val := rfl

/-- Pair the actual radical matrices and their inverses in the full adele ring. -/
def pair (a : Infinite F B) (b : Finite F B) : Full F B :=
  ⟨AdelicBlockParabolic.pair F B a.val b.val, by
    change B.leviProjection (AdeleRing (𝓞 F) F) (AdelicBlockParabolic.pair F B a.val b.val) = 1
    rw [AdelicBlockParabolic.leviProjection_pair, a.property, b.property]
    exact (AdelicBlockParabolic.leviSplit F B).symm.map_one⟩

@[simp] theorem pair_val (a : Infinite F B) (b : Finite F B) :
    (pair F B a b).val = AdelicBlockParabolic.pair F B a.val b.val := rfl

@[simp] theorem infinite_pair (a : Infinite F B) (b : Finite F B) :
    infinite F B (pair F B a b) = a :=
  Subtype.ext (AdelicBlockParabolic.infinite_pair F B a.val b.val)

@[simp] theorem finite_pair (a : Infinite F B) (b : Finite F B) :
    finite F B (pair F B a b) = b :=
  Subtype.ext (AdelicBlockParabolic.finite_pair F B a.val b.val)

@[simp] theorem pair_projections (u : Full F B) :
    pair F B (infinite F B u) (finite F B u) = u :=
  Subtype.ext (AdelicBlockParabolic.pair_projections F B u.val)

theorem continuous_pair :
    Continuous (fun p : Infinite F B × Finite F B => pair F B p.1 p.2) :=
  ((AdelicBlockParabolic.continuous_pair F B).comp
    ((continuous_subtype_val.comp continuous_fst).prodMk
      (continuous_subtype_val.comp continuous_snd))).subtype_mk _

/-- A genuine multiplicative homeomorphism of the actual full radical with its factors. -/
def split : Full F B ≃ₜ* Infinite F B × Finite F B where
  toFun u := (infinite F B u, finite F B u)
  invFun p := pair F B p.1 p.2
  left_inv := pair_projections F B
  right_inv p := Prod.ext (infinite_pair F B p.1 p.2) (finite_pair F B p.1 p.2)
  map_mul' u v := Prod.ext ((infinite F B).map_mul u v) ((finite F B).map_mul u v)
  continuous_toFun := (infinite F B).continuous.prodMk (finite F B).continuous
  continuous_invFun := continuous_pair F B

/-- Include the archimedean radical with identity in the finite component. -/
def ofInfinite : Infinite F B →ₜ* Full F B :=
  (ContinuousMonoidHom.toContinuousMonoidHom (split F B).symm).comp
    (ContinuousMonoidHom.inl _ _)

/-- Include the finite radical with identity in the archimedean component. -/
def ofFinite : Finite F B →ₜ* Full F B :=
  (ContinuousMonoidHom.toContinuousMonoidHom (split F B).symm).comp
    (ContinuousMonoidHom.inr _ _)

/-- The radical splitting commutes with its actual inclusion into the parabolic. -/
theorem split_val (u : Full F B) :
    AdelicBlockParabolic.split F B u.val = ((split F B u).1.val, (split F B u).2.val) := rfl

/-- Archimedean projection intertwines actual conjugation by the block Levi. -/
@[simp] theorem infinite_leviAction (m : AdelicBlockParabolic.FullLevi F B) (u : Full F B) :
    infinite F B (B.leviAction (AdeleRing (𝓞 F) F) m u) =
      B.leviAction (InfiniteAdeleRing F) (AdelicBlockParabolic.leviInfinite F B m) (infinite F B u) := by
  apply Subtype.ext
  change AdelicBlockParabolic.infinite F B
      (B.leviInParabolic (AdeleRing (𝓞 F) F) m * u.val *
        (B.leviInParabolic (AdeleRing (𝓞 F) F) m)⁻¹) =
    B.leviInParabolic (InfiniteAdeleRing F) (AdelicBlockParabolic.leviInfinite F B m) *
      (infinite F B u).val *
        (B.leviInParabolic (InfiniteAdeleRing F) (AdelicBlockParabolic.leviInfinite F B m))⁻¹
  simp only [map_mul, map_inv, AdelicBlockParabolic.infinite_leviInParabolic, infinite_val]

/-- Finite projection intertwines actual conjugation by the block Levi. -/
@[simp] theorem finite_leviAction (m : AdelicBlockParabolic.FullLevi F B) (u : Full F B) :
    finite F B (B.leviAction (AdeleRing (𝓞 F) F) m u) =
      B.leviAction (FiniteAdeleRing (𝓞 F) F) (AdelicBlockParabolic.leviFinite F B m) (finite F B u) := by
  apply Subtype.ext
  change AdelicBlockParabolic.finite F B
      (B.leviInParabolic (AdeleRing (𝓞 F) F) m * u.val *
        (B.leviInParabolic (AdeleRing (𝓞 F) F) m)⁻¹) =
    B.leviInParabolic (FiniteAdeleRing (𝓞 F) F) (AdelicBlockParabolic.leviFinite F B m) *
      (finite F B u).val *
        (B.leviInParabolic (FiniteAdeleRing (𝓞 F) F) (AdelicBlockParabolic.leviFinite F B m))⁻¹
  simp only [map_mul, map_inv, AdelicBlockParabolic.finite_leviInParabolic, finite_val]

/-- The radical and Levi splittings respect their actual conjugation action. -/
theorem split_leviAction (m : AdelicBlockParabolic.FullLevi F B) (u : Full F B) :
    split F B (B.leviAction (AdeleRing (𝓞 F) F) m u) =
      (B.leviAction (InfiniteAdeleRing F) (AdelicBlockParabolic.leviSplit F B m).1 (split F B u).1,
        B.leviAction (FiniteAdeleRing (𝓞 F) F) (AdelicBlockParabolic.leviSplit F B m).2 (split F B u).2) :=
  Prod.ext (infinite_leviAction F B m u) (finite_leviAction F B m u)

/-- Removing the actual Levi part commutes with archimedean projection. -/
@[simp] theorem infinite_unipotentPart (g : AdelicBlockParabolic.Full F B) :
    infinite F B (B.unipotentPart (AdeleRing (𝓞 F) F) g) =
      B.unipotentPart (InfiniteAdeleRing F) (AdelicBlockParabolic.infinite F B g) := by
  apply Subtype.ext
  change AdelicBlockParabolic.infinite F B
      (g * (B.leviInParabolic (AdeleRing (𝓞 F) F)
        (B.leviProjection (AdeleRing (𝓞 F) F) g))⁻¹) =
    AdelicBlockParabolic.infinite F B g * (B.leviInParabolic (InfiniteAdeleRing F)
      (B.leviProjection (InfiniteAdeleRing F) (AdelicBlockParabolic.infinite F B g)))⁻¹
  simp only [map_mul, map_inv, AdelicBlockParabolic.infinite_leviInParabolic, AdelicBlockParabolic.leviProjection_infinite]

/-- Removing the actual Levi part commutes with finite projection. -/
@[simp] theorem finite_unipotentPart (g : AdelicBlockParabolic.Full F B) :
    finite F B (B.unipotentPart (AdeleRing (𝓞 F) F) g) =
      B.unipotentPart (FiniteAdeleRing (𝓞 F) F) (AdelicBlockParabolic.finite F B g) := by
  apply Subtype.ext
  change AdelicBlockParabolic.finite F B
      (g * (B.leviInParabolic (AdeleRing (𝓞 F) F)
        (B.leviProjection (AdeleRing (𝓞 F) F) g))⁻¹) =
    AdelicBlockParabolic.finite F B g * (B.leviInParabolic (FiniteAdeleRing (𝓞 F) F)
      (B.leviProjection (FiniteAdeleRing (𝓞 F) F) (AdelicBlockParabolic.finite F B g)))⁻¹
  simp only [map_mul, map_inv, AdelicBlockParabolic.finite_leviInParabolic, AdelicBlockParabolic.leviProjection_finite]

/-- The unique `u*m` coordinates commute with archimedean projection. -/
theorem decomposition_infinite (g : AdelicBlockParabolic.Full F B) :
    B.decomposition (InfiniteAdeleRing F) (AdelicBlockParabolic.infinite F B g) =
      (infinite F B (B.decomposition (AdeleRing (𝓞 F) F) g).1,
        AdelicBlockParabolic.leviInfinite F B (B.decomposition (AdeleRing (𝓞 F) F) g).2) :=
  Prod.ext (infinite_unipotentPart F B g).symm (AdelicBlockParabolic.leviProjection_infinite F B g)

/-- The unique `u*m` coordinates commute with finite projection. -/
theorem decomposition_finite (g : AdelicBlockParabolic.Full F B) :
    B.decomposition (FiniteAdeleRing (𝓞 F) F) (AdelicBlockParabolic.finite F B g) =
      (finite F B (B.decomposition (AdeleRing (𝓞 F) F) g).1,
        AdelicBlockParabolic.leviFinite F B (B.decomposition (AdeleRing (𝓞 F) F) g).2) :=
  Prod.ext (finite_unipotentPart F B g).symm (AdelicBlockParabolic.leviProjection_finite F B g)

end Langlands.Global.AdelicBlockUnipotent
