import Langlands.AbelianScheme.FiniteDvrExtensionHenselian
import Langlands.AbelianScheme.FiniteDvrExtensionResidue
import Langlands.AbelianScheme.Tate.ModelMonodromy
import Langlands.AlgebraicGeometry.FiniteEtale.StrictLocalCover
import Langlands.Shimura.PEL.HarrisTaylorCMDivisionPotentialReduction

/-! # Finite-order rational monodromy after potential good reduction over a strict trait -/

noncomputable section

open CategoryTheory AlgebraicGeometry IsLocalRing Langlands.AlgebraicGeometry.FiniteEtale

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace Langlands.AbelianScheme

open Tate
open GroupScheme.Tate (Index)

/-- A uniform positive exponent for the rational Tate monodromy of a potentially
good abelian variety over the fraction field of a strictly Henselian DVR of
residue characteristic zero. -/
def HasPotentialGoodReduction.strictLocalMonodromyExponent
    {V K : Type u} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
    [HenselianLocalRing V] [CharZero (ResidueField V)] [IsSepClosed (ResidueField V)]
    [Field K] [Algebra V K] [IsFractionRing V K]
    {B : AbelianScheme (Spec (.of K))} (h : HasPotentialGoodReduction (V := V) B)
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ Spec (.of K))
    (htor : TorsionFiniteEtaleStatement.{u}) (P : ℕ → Prop)
    (hu : ∀ n : Index P, IsUnit (n.val : Γ(Spec (.of K), ⊤))) :
    {m : ℕ // 0 < m ∧ ∀ g : FundamentalGroup s (geometricFiberFinite s),
      (rationalMonodromyRepresentation s (geometricFiberFinite s) htor B P hu g) ^ m = 1} := by
  let E := Classical.choose h
  let G := Classical.choose (Classical.choose_spec h)
  let e := Classical.choice (Classical.choose_spec (Classical.choose_spec h))
  let L := E.fractionField
  let : Module.Finite K L := E.finite
  let : CharZero V := ⟨fun a b hab =>
    Nat.cast_injective (R := ResidueField V)
      (by simpa only [map_natCast] using congrArg (residue V) hab)⟩
  let : CharZero K := charZero_of_injective_algebraMap (IsFractionRing.injective V K)
  let : HenselianLocalRing E.ring := E.henselian_ring
  let : CharZero (ResidueField E.ring) := E.charZero_residue
  let : IsAlgClosed (ResidueField E.ring) := E.isAlgClosed_residue
  let Y := fieldExtensionCover K L
  let x := fieldExtensionCoverPoint K L s
  let j := NeronModelInfra.specGenericFibreInclusion E.ring L
  let hs := geometricFiberFinite s
  let hw := geometricFiberFinite x.left
  let ht := geometricFiberFinite (x.left ≫ j)
  let ρ := rationalMonodromyRepresentation s hs htor B P hu
  let : Subsingleton (FundamentalGroup (x.left ≫ j) ht) :=
    subsingleton_fundamentalGroup_of_strictLocal E.ring _ ht
  let : Finite (Fiber s Y) := hs Y
  have huT (n : Index P) : IsUnit (n.val : Γ(Spec (.of E.ring), ⊤)) := by
    simpa only [map_natCast] using
      (isUnit_natCast_of_charZero_residue E.ring n.property.1).map
        (Scheme.ΓSpecIso (.of E.ring)).inv.hom
  have huW (n : Index P) : IsUnit (n.val : Γ(Y.obj.left, ⊤)) := by
    simpa only [map_natCast] using (hu n).map Y.obj.hom.appTop.hom
  refine ⟨Nat.card (Equiv.Perm (Fiber s Y)), Finite.card_pos, ?_⟩
  intro g
  change (ρ g) ^ Nat.card (Equiv.Perm (Fiber s Y)) = 1
  let k := liftPowerToCover s hs Y x hw g
  rw [← map_pow, ← k.property]
  exact rationalMonodromy_eq_one_of_model Y.obj.hom j B G e x.left s (Over.w x) P
    hw hs ht htor hu huT huW k.val (Subsingleton.elim _ _)

end Langlands.AbelianScheme
