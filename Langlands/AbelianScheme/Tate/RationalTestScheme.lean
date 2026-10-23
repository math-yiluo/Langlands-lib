import Langlands.AbelianScheme.Tate.TestScheme
import Langlands.AbelianScheme.Tate.AwayRationalScalars

noncomputable section
open CategoryTheory AlgebraicGeometry
open scoped TensorProduct

namespace Langlands.GroupScheme.Tate
universe u
variable {S : Scheme.{u}} (G : Grp (Over S)) [IsCommMonObj G.X]
variable {T T' T'' : Over S}

/-- Rationalization of actual test-scheme restriction. -/
def rationalTestRestrict (P : ℕ → Prop) (a : T' ⟶ T) :
    Rational G T P →ₗ[ℚ] Rational G T' P :=
  (testRestrict G P a).toIntLinearMap.baseChange ℚ

@[simp] theorem rationalTestRestrict_tmul (P : ℕ → Prop) (a : T' ⟶ T)
    (q : ℚ) (x : Integral G T P) :
    rationalTestRestrict G P a (q ⊗ₜ[ℤ] x) = q ⊗ₜ[ℤ] testRestrict G P a x := rfl

@[simp] theorem rationalTestRestrict_toRational (P : ℕ → Prop) (a : T' ⟶ T)
    (x : Integral G T P) :
    rationalTestRestrict G P a (toRational G T P x) =
      toRational G T' P (testRestrict G P a x) := rfl

@[simp] theorem rationalTestRestrict_id (P : ℕ → Prop) :
    rationalTestRestrict G P (𝟙 T) = LinearMap.id := by
  apply TensorProduct.AlgebraTensorModule.ext
  intro q x
  simp

/-- Restriction remains contravariant after rationalization. -/
theorem rationalTestRestrict_comp (P : ℕ → Prop) (a : T' ⟶ T) (b : T'' ⟶ T') :
    rationalTestRestrict G P (b ≫ a) =
      (rationalTestRestrict G P b).comp (rationalTestRestrict G P a) := by
  apply TensorProduct.AlgebraTensorModule.ext
  intro q x
  simp [testRestrict_comp]

/-- Test-scheme restriction commutes with selecting the away orders. -/
theorem rationalTestRestrict_restrictAway (m : ℕ) (a : T' ⟶ T)
    (x : RationalFull G T) :
    rationalTestRestrict G (fun n => Nat.Coprime n m) a (rationalRestrictAway G T m x) =
      rationalRestrictAway G T' m (rationalTestRestrict G (fun _ => True) a x) := by
  induction x using TensorProduct.inductionOn with
  | tmul q x => rfl
  | add x y hx hy => simp_all

/-- Rationalized full residue scalars commute with restriction. -/
theorem rationalTestRestrict_scalarAction (P : ℕ → Prop) (a : T' ⟶ T)
    (r : ℚ ⊗[ℤ] Global.ProfiniteIntegerRing) (x : Rational G T P) :
    rationalTestRestrict G P a (rationalScalarAction G T P r x) =
      rationalScalarAction G T' P r (rationalTestRestrict G P a x) :=
  TateScalarExtension.map_action (fullTestRestrict G P a).toLinearMap r x

/-- The existing finite-adelic action is preserved with the same comparison hypothesis. -/
theorem rationalTestRestrict_finiteAdeleAction (P : ℕ → Prop) (a : T' ⟶ T)
    (h : Global.RationalProfiniteIntegerAdeleComparison)
    (r : Global.FiniteAdeles ℚ) (x : Rational G T P) :
    rationalTestRestrict G P a (finiteAdeleAction G T P h r x) =
      finiteAdeleAction G T' P h r (rationalTestRestrict G P a x) :=
  rationalTestRestrict_scalarAction G P a _ x

/-- Restriction bundled over the existing finite-adelic scalar ring. -/
def finiteAdeleTestRestrict (P : ℕ → Prop) (a : T' ⟶ T)
    (h : Global.RationalProfiniteIntegerAdeleComparison) :
    let := finiteAdeleModule G T P h
    let := finiteAdeleModule G T' P h
    Rational G T P →ₗ[Global.FiniteAdeles ℚ] Rational G T' P := by
  let := finiteAdeleModule G T P h
  let := finiteAdeleModule G T' P h
  exact { (rationalTestRestrict G P a).toAddHom with
    map_smul' := rationalTestRestrict_finiteAdeleAction G P a h }

@[simp] theorem finiteAdeleTestRestrict_apply (P : ℕ → Prop) (a : T' ⟶ T)
    (h : Global.RationalProfiniteIntegerAdeleComparison) (x : Rational G T P) :
    finiteAdeleTestRestrict G P a h x = rationalTestRestrict G P a x := rfl

/-- The actual away residue action is preserved after rationalization. -/
theorem rationalTestRestrict_awayScalarAction (m : ℕ) (a : T' ⟶ T)
    (r : ℚ ⊗[ℤ] Global.PrimeToProfiniteIntegerRing m) (x : RationalAway G T m) :
    rationalTestRestrict G (fun n => Nat.Coprime n m) a (rationalAwayScalarAction G T m r x) =
      rationalAwayScalarAction G T' m r
        (rationalTestRestrict G (fun n => Nat.Coprime n m) a x) :=
  TateScalarExtension.map_action (awayTestRestrict G m a).toLinearMap r x

variable {h : Global.RationalProfiniteIntegerAdeleComparison} {m : ℕ}

/-- The coupled away finite-adelic action is preserved. -/
theorem rationalTestRestrict_primeToFiniteAdeleAction (a : T' ⟶ T)
    (hAway : Global.PrimeToRationalProfiniteIntegerAdeleComparison h m)
    (r : Global.PrimeToFiniteAdeles m) (x : RationalAway G T m) :
    rationalTestRestrict G (fun n => Nat.Coprime n m) a (primeToFiniteAdeleAction G T hAway r x) =
      primeToFiniteAdeleAction G T' hAway r
        (rationalTestRestrict G (fun n => Nat.Coprime n m) a x) :=
  rationalTestRestrict_awayScalarAction G m a _ x

/-- Away restriction bundled with the same explicit comparison witnesses. -/
def primeToFiniteAdeleTestRestrict (a : T' ⟶ T)
    (hAway : Global.PrimeToRationalProfiniteIntegerAdeleComparison h m) :
    let := primeToFiniteAdeleModule G T hAway
    let := primeToFiniteAdeleModule G T' hAway
    RationalAway G T m →ₗ[Global.PrimeToFiniteAdeles m] RationalAway G T' m := by
  let := primeToFiniteAdeleModule G T hAway
  let := primeToFiniteAdeleModule G T' hAway
  exact { (rationalTestRestrict G (fun n => Nat.Coprime n m) a).toAddHom with
    map_smul' := rationalTestRestrict_primeToFiniteAdeleAction G a hAway }

@[simp] theorem primeToFiniteAdeleTestRestrict_apply (a : T' ⟶ T)
    (hAway : Global.PrimeToRationalProfiniteIntegerAdeleComparison h m)
    (x : RationalAway G T m) :
    primeToFiniteAdeleTestRestrict G a hAway x =
      rationalTestRestrict G (fun n => Nat.Coprime n m) a x := rfl

variable {G} {H : Grp (Over S)} [IsCommMonObj H.X]

/-- Restriction commutes with rationalized group-scheme homomorphisms. -/
theorem rationalTestRestrict_map (P : ℕ → Prop) (a : T' ⟶ T) (f : G ⟶ H)
    (x : Rational G T P) :
    rationalTestRestrict H P a (rationalMap T P f x) =
      rationalMap T' P f (rationalTestRestrict G P a x) := by
  induction x using TensorProduct.inductionOn with
  | tmul q x => simp only [rationalMap_tmul, rationalTestRestrict_tmul, testRestrict_map]
  | add x y hx hy => simp_all

end Langlands.GroupScheme.Tate

namespace Langlands.AbelianScheme.Tate
universe u
variable {S : Scheme.{u}} (A : AbelianScheme S) {T T' : Over S} (P : ℕ → Prop)

/-- Test-scheme restriction for an actual abelian scheme. -/
abbrev rationalTestRestrict (a : T' ⟶ T) : Rational A T P →ₗ[ℚ] Rational A T' P :=
  GroupScheme.Tate.rationalTestRestrict A.toGrp P a

variable {A} {B : AbelianScheme S}

/-- Naturality for actual abelian-scheme homomorphisms. -/
theorem rationalTestRestrict_map (a : T' ⟶ T) (f : A ⟶ B) (x : Rational A T P) :
    rationalTestRestrict B P a (rationalMap T P f x) =
      rationalMap T' P f (rationalTestRestrict A P a x) :=
  GroupScheme.Tate.rationalTestRestrict_map P a (AbelianScheme.groupHom f) x

/-- Naturality extends to actual rational homomorphisms. -/
theorem rationalTestRestrict_homMap (a : T' ⟶ T) (f : Rationalization.Hom A B)
    (x : Rational A T P) :
    rationalTestRestrict B P a (rationalHomMap T P f x) =
      rationalHomMap T' P f (rationalTestRestrict A P a x) := by
  induction f using TensorProduct.inductionOn with
  | tmul q f => simp [rationalTestRestrict_map]
  | add f g hf hg => simp_all

/-- Rational-isogeny transport commutes with restriction. -/
theorem rationalTestRestrict_iso (a : T' ⟶ T)
    (e : Rationalization.of A ≅ Rationalization.of B) (x : Rational A T P) :
    rationalTestRestrict B P a (rationalIso T P e x) =
      rationalIso T' P e (rationalTestRestrict A P a x) :=
  rationalTestRestrict_homMap P a e.hom x

end Langlands.AbelianScheme.Tate
