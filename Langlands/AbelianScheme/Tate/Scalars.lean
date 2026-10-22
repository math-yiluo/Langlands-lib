import Langlands.AbelianScheme.Tate.PrimeAdic
import Langlands.AbelianScheme.Tate.AbelianScheme
import Langlands.Global.ProfiniteIntegerRing

/-! # Full and prime-to-p scalar actions on integral Tate modules -/

noncomputable section
open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.Tate
universe u
variable {S : Scheme.{u}} (G : Grp (Over S)) [IsCommMonObj G.X] (T : Over S)

namespace ScalarAction
variable (P : ℕ → Prop) {R : Type*} [CommRing R]
variable (r : ∀ n : Index P, R →+* ZMod n.val)
variable (hr : ∀ n m (h : n.val ∣ m.val),
  (ZMod.castHom h (ZMod n.val)).comp (r m) = r n)

/-- Compatible residue scalars act on the existing coherent-family limit. -/
@[instance_reducible] def module : Module R (Integral G T P) where
  smul a x := ⟨fun n => r n a • x.val n, by
    intro n m h
    rw [transition_zmod_smul, x.property n m h]
    exact congrArg (fun b => b • x.val n) (DFunLike.congr_fun (hr n m h) a)⟩
  one_smul x := by
    apply Subtype.ext; funext n
    change r n 1 • x.val n = x.val n
    rw [map_one, one_smul]
  mul_smul a b x := by
    apply Subtype.ext; funext n
    change r n (a * b) • x.val n = r n a • (r n b • x.val n)
    rw [_root_.map_mul, mul_smul]
  smul_zero a := by apply Subtype.ext; funext n; exact smul_zero _
  smul_add a x y := by apply Subtype.ext; funext n; exact smul_add _ _ _
  add_smul a b x := by
    apply Subtype.ext; funext n
    change r n (a + b) • x.val n = r n a • x.val n + r n b • x.val n
    rw [map_add, add_smul]
  zero_smul x := by
    apply Subtype.ext; funext n
    change r n 0 • x.val n = 0
    rw [map_zero, zero_smul]

variable {P r hr}

/-- Continuity is inherited from continuous residue maps and discrete torsion levels. -/
theorem continuous_smul [TopologicalSpace R] (hc : ∀ n, Continuous (r n)) :
    let := module G T P r hr
    Continuous (fun z : R × Integral G T P => z.1 • z.2) := by
  let := module G T P r hr
  apply Continuous.subtype_mk
  apply continuous_pi
  intro n
  exact (continuous_of_discreteTopology
    (f := fun z : ZMod n.val × Level G T n.val => z.1 • z.2)).comp
      (((hc n).comp continuous_fst).prodMk
        ((continuous_evaluation G T P n).comp continuous_snd))

/-- The induced group-scheme map preserves every compatible residue action. -/
theorem map_smul {H : Grp (Over S)} [IsCommMonObj H.X] (f : G ⟶ H) (a : R)
    (x : Integral G T P) :
    let := module G T P r hr
    let := module H T P r hr
    map T P f (a • x) = a • map T P f x := by
  let := module G T P r hr
  let := module H T P r hr
  apply Subtype.ext
  funext n
  change levelMap T f n.val (r n a • x.val n) = r n a • levelMap T f n.val (x.val n)
  obtain ⟨z, hz⟩ := ZMod.intCast_surjective (r n a)
  rw [← hz]
  simp only [Int.cast_smul_eq_zsmul, map_zsmul]

end ScalarAction

/-- Reduction of a full profinite scalar at a selected positive torsion level. -/
def fullReduction (P : ℕ → Prop) (n : Index P) :
    Global.ProfiniteIntegerRing →+* ZMod n.val :=
  Global.ProfiniteIntegerRing.reduction ⟨n.val, n.property.1⟩

lemma fullReduction_compatible (P : ℕ → Prop) (n m : Index P) (h : n.val ∣ m.val) :
    (ZMod.castHom h (ZMod n.val)).comp (fullReduction P m) = fullReduction P n :=
  Global.ResidueLimit.transition_comp_reduction
    (modulus := fun n : ℕ+ => n) ⟨n.val, n.property.1⟩ ⟨m.val, m.property.1⟩ h

/-- Every selected Tate limit is a module over the full profinite-integer ring. -/
instance fullModule (P : ℕ → Prop) : Module Global.ProfiniteIntegerRing (Integral G T P) :=
  ScalarAction.module G T P (fullReduction P) (fullReduction_compatible P)

@[simp] theorem evaluation_full_smul (P : ℕ → Prop) (n : Index P)
    (a : Global.ProfiniteIntegerRing) (x : Integral G T P) :
    evaluation G T P n (a • x) = fullReduction P n a • evaluation G T P n x := rfl

instance fullContinuousSMul (P : ℕ → Prop) :
    ContinuousSMul Global.ProfiniteIntegerRing (Integral G T P) :=
  ⟨ScalarAction.continuous_smul G T (r := fullReduction P)
    (hr := fullReduction_compatible P) (fun _ => Global.ResidueLimit.continuous_reduction _)⟩

/-- Reduction of a prime-to-p scalar at the corresponding torsion level. -/
def awayReduction (p : ℕ) (n : Index (fun n => Nat.Coprime n p)) :
    Global.PrimeToProfiniteIntegerRing p →+* ZMod n.val :=
  Global.PrimeToProfiniteIntegerRing.reduction ⟨⟨n.val, n.property.1⟩, n.property.2⟩

lemma awayReduction_compatible (p : ℕ) (n m : Index (fun n => Nat.Coprime n p))
    (h : n.val ∣ m.val) :
    (ZMod.castHom h (ZMod n.val)).comp (awayReduction p m) = awayReduction p n :=
  Global.ResidueLimit.transition_comp_reduction
    (modulus := fun n : Global.PrimeToModulus p => n.val)
    ⟨⟨n.val, n.property.1⟩, n.property.2⟩ ⟨⟨m.val, m.property.1⟩, m.property.2⟩ h

instance awayModule (p : ℕ) : Module (Global.PrimeToProfiniteIntegerRing p) (Away G T p) :=
  ScalarAction.module G T _ (awayReduction p) (awayReduction_compatible p)

@[simp] theorem evaluation_away_smul (p : ℕ) (n : Index (fun n => Nat.Coprime n p))
    (a : Global.PrimeToProfiniteIntegerRing p) (x : Away G T p) :
    evaluation G T _ n (a • x) = awayReduction p n a • evaluation G T _ n x := rfl

instance awayContinuousSMul (p : ℕ) :
    ContinuousSMul (Global.PrimeToProfiniteIntegerRing p) (Away G T p) :=
  ⟨ScalarAction.continuous_smul G T (r := awayReduction p)
    (hr := awayReduction_compatible p) (fun _ => Global.ResidueLimit.continuous_reduction _)⟩

/-- Integer scalars have their usual additive meaning. -/
theorem full_intCast_smul (P : ℕ → Prop) (z : ℤ) (x : Integral G T P) :
    (z : Global.ProfiniteIntegerRing) • x = z • x := by
  apply Subtype.ext
  funext n
  change fullReduction P n (z : Global.ProfiniteIntegerRing) • x.val n = z • x.val n
  rw [map_intCast, Int.cast_smul_eq_zsmul]

theorem away_intCast_smul (p : ℕ) (z : ℤ) (x : Away G T p) :
    (z : Global.PrimeToProfiniteIntegerRing p) • x = z • x := by
  apply Subtype.ext
  funext n
  change awayReduction p n (z : Global.PrimeToProfiniteIntegerRing p) • x.val n = z • x.val n
  rw [map_intCast, Int.cast_smul_eq_zsmul]

/-- Restriction uses the corresponding restriction of the scalar ring. -/
theorem restrictAway_smul (p : ℕ) (a : Global.ProfiniteIntegerRing) (x : Full G T) :
    restrictAway G T p (a • x) = Global.PrimeToProfiniteIntegerRing.restrict p a •
      restrictAway G T p x := rfl

/-- The full-ring action on an away limit agrees with its restricted scalar action. -/
theorem full_smul_eq_away_smul (p : ℕ) (a : Global.ProfiniteIntegerRing) (x : Away G T p) :
    a • x = Global.PrimeToProfiniteIntegerRing.restrict p a • x := rfl

variable {G} {H : Grp (Over S)} [IsCommMonObj H.X]

/-- The existing Tate map, now bundled as a profinite-integer linear map. -/
def fullLinearMap (P : ℕ → Prop) (f : G ⟶ H) :
    Integral G T P →ₗ[Global.ProfiniteIntegerRing] Integral H T P where
  toAddHom := map T P f
  map_smul' := ScalarAction.map_smul G T (r := fullReduction P)
    (hr := fullReduction_compatible P) f

/-- The existing prime-to-p Tate map is linear over the away scalar ring. -/
def awayLinearMap (p : ℕ) (f : G ⟶ H) :
    Away G T p →ₗ[Global.PrimeToProfiniteIntegerRing p] Away H T p where
  toAddHom := map T (fun n => Nat.Coprime n p) f
  map_smul' := ScalarAction.map_smul G T (r := awayReduction p)
    (hr := awayReduction_compatible p) f

end Langlands.GroupScheme.Tate

namespace Langlands.AbelianScheme.Tate
universe u
variable {S : Scheme.{u}} (T : Over S) {A B : AbelianScheme S}

/-- Profinite-integer linear map induced by an actual abelian-scheme homomorphism. -/
abbrev fullLinearMap (P : ℕ → Prop) (f : A ⟶ B) :
    Integral A T P →ₗ[Global.ProfiniteIntegerRing] Integral B T P :=
  GroupScheme.Tate.fullLinearMap T P (AbelianScheme.groupHom f)

/-- Prime-to-p linear map induced by an actual abelian-scheme homomorphism. -/
abbrev awayLinearMap (p : ℕ) (f : A ⟶ B) :
    Away A T p →ₗ[Global.PrimeToProfiniteIntegerRing p] Away B T p :=
  GroupScheme.Tate.awayLinearMap T p (AbelianScheme.groupHom f)

end Langlands.AbelianScheme.Tate
