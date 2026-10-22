import Langlands.WeilDeligne.Basic
import Langlands.Weil.Representation.Induction

/-!
# Finite-index induction of Weil–Deligne pairs

For right translation on equivariant functions, the induced monodromy is
`(N f)(g) = ν(g) • N(f(g))`. This weight is forced by the norm covariance.
-/

noncomputable section

universe uK uG uV

open CategoryTheory

namespace Langlands.WeilDeligneRepresentation

variable {K : Type uK} {G : Type uG} [Field K] [Group G] {ν : G →* Kˣ}

namespace Induction

/-- Covariance expressed without an inverse action on the input. -/
theorem action_monodromy (A : WeilDeligneRepresentation K G ν) (g : G) (x : A) :
    A.representation g (A.monodromy x) =
      (ν g : K) • A.monodromy (A.representation g x) := by
  have hi : A.representation g⁻¹ (A.representation g x) = x := by
    change (A.representation g⁻¹ * A.representation g) x = x
    rw [← map_mul, inv_mul_cancel, map_one]
    rfl
  have h := LinearMap.congr_fun (A.covariance g) (A.representation g x)
  simpa only [Module.End.mul_apply, LinearMap.smul_apply, hi] using h

/-- Weighted pointwise monodromy on Mathlib's equivariant function space.
Its preservation of that space follows from the original covariance law. -/
def monodromy (S : Subgroup G)
    (A : WeilDeligneRepresentation.{uK, uG, uV} K S (ν.comp S.subtype)) :
    Module.End K (Representation.coindV S.subtype A.representation) where
  toFun f := ⟨fun g => (ν g : K) • A.monodromy (f.val g), by
    intro s g
    change (ν ((s : G) * g) : K) • A.monodromy (f.val ((s : G) * g)) =
      A.representation s ((ν g : K) • A.monodromy (f.val g))
    have hf : f.val ((s : G) * g) = A.representation s (f.val g) := f.property s g
    rw [hf, map_smul, action_monodromy A s]
    simp only [MonoidHom.comp_apply, Subgroup.coe_subtype, map_mul, Units.val_mul,
      smul_smul]
    rw [mul_comm]⟩
  map_add' f g := by
    apply Subtype.ext
    funext x
    exact congrArg ((ν x : K) • ·) (map_add A.monodromy (f.val x) (g.val x)) |>.trans
      (smul_add _ _ _)
  map_smul' a f := by
    apply Subtype.ext
    funext x
    change (ν x : K) • A.monodromy (a • f.val x) =
      a • ((ν x : K) • A.monodromy (f.val x))
    rw [map_smul, smul_comm]

@[simp]
theorem monodromy_apply (S : Subgroup G)
    (A : WeilDeligneRepresentation.{uK, uG, uV} K S (ν.comp S.subtype))
    (f : Representation.coindV S.subtype A.representation) (g : G) :
    (monodromy S A f).val g = (ν g : K) • A.monodromy (f.val g) := rfl

/-- Every monodromy power is computed pointwise with the corresponding norm power. -/
theorem monodromy_pow_apply (S : Subgroup G)
    (A : WeilDeligneRepresentation.{uK, uG, uV} K S (ν.comp S.subtype))
    (n : ℕ) (f : Representation.coindV S.subtype A.representation) (g : G) :
    (((monodromy S A)^n) f).val g = (ν g : K)^n • (A.monodromy^n) (f.val g) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ', Module.End.mul_apply, monodromy_apply, ih, map_smul]
    simp only [smul_smul, pow_succ', Module.End.mul_apply]

/-- Induction preserves the original nilpotence exponent. -/
theorem monodromy_nilpotent (S : Subgroup G)
    (A : WeilDeligneRepresentation.{uK, uG, uV} K S (ν.comp S.subtype)) :
    IsNilpotent (monodromy S A) := by
  obtain ⟨n, hn⟩ := A.nilpotent
  refine ⟨n, ?_⟩
  apply LinearMap.ext
  intro f
  apply Subtype.ext
  funext g
  rw [monodromy_pow_apply, hn]
  simp

/-- Right translation conjugates the weighted monodromy by the supplied norm. -/
theorem covariance (S : Subgroup G)
    (A : WeilDeligneRepresentation.{uK, uG, uV} K S (ν.comp S.subtype)) (h : G) :
    Representation.coind S.subtype A.representation h * monodromy S A *
      Representation.coind S.subtype A.representation h⁻¹ =
        (ν h : K) • monodromy S A := by
  apply LinearMap.ext
  intro f
  apply Subtype.ext
  funext g
  change (ν (g * h) : K) • A.monodromy (f.val (g * h * h⁻¹)) =
    (ν h : K) • ((ν g : K) • A.monodromy (f.val g))
  simp only [mul_inv_cancel_right, map_mul, Units.val_mul, smul_smul]
  rw [mul_comm]

end Induction

variable (S : Subgroup G) [S.FiniteIndex]

/-- Actual finite-index induction of a Weil–Deligne pair. -/
def induce (A : WeilDeligneRepresentation.{uK, uG, uV} K S (ν.comp S.subtype)) :
    WeilDeligneRepresentation.{uK, uG, max uG uV} K G ν where
  toFiniteRepresentation := FiniteRepresentation.induce S A.toFiniteRepresentation
  monodromy := Induction.monodromy S A
  nilpotent := Induction.monodromy_nilpotent S A
  covariance := Induction.covariance S A

@[simp]
theorem induce_monodromy_apply
    (A : WeilDeligneRepresentation.{uK, uG, uV} K S (ν.comp S.subtype))
    (f : induce S A) (g : G) :
    ((induce S A).monodromy f).val g = (ν g : K) • A.monodromy (f.val g) := rfl

/-- Induction on pair morphisms is pointwise application, which commutes with the
weighted monodromy by linearity and the original monodromy square. -/
def induceMap
    {A B : WeilDeligneRepresentation.{uK, uG, uV} K S (ν.comp S.subtype)}
    (f : Hom A B) : Hom (induce S A) (induce S B) where
  intertwiner := FiniteRepresentation.induceMap S f.intertwiner
  comm_monodromy := by
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    funext g
    change f.intertwiner ((ν g : K) • A.monodromy (x.val g)) =
      (ν g : K) • B.monodromy (f.intertwiner (x.val g))
    rw [map_smul]
    exact congrArg ((ν g : K) • ·) (LinearMap.congr_fun f.comm_monodromy (x.val g))

/-- Induction is a functor on the actual pair categories. -/
def induceFunctor :
    WeilDeligneRepresentation.{uK, uG, uV} K S (ν.comp S.subtype) ⥤
      WeilDeligneRepresentation.{uK, uG, max uG uV} K G ν where
  obj := induce S
  map := induceMap S
  map_id _ := by apply Hom.ext; rfl
  map_comp _ _ := by apply Hom.ext; rfl

/-- Induction of actual pair equivalences. -/
def induceEquiv
    {A B : WeilDeligneRepresentation.{uK, uG, uV} K S (ν.comp S.subtype)}
    (e : Equiv A B) : Equiv (induce S A) (induce S B) :=
  Equiv.ofIso ((induceFunctor S).mapIso e.toIso)

/-- Finite-index induction on genuine pair isomorphism classes. -/
def induceClass :
    IsomorphismClasses.{uK, uG, uV} K S (ν.comp S.subtype) →
      IsomorphismClasses.{uK, uG, max uG uV} K G ν :=
  Quotient.map (induce S) (fun _ _ ⟨e⟩ => ⟨induceEquiv S e⟩)

/-- The rank of an induced pair, allowing zero rank. -/
theorem rank_induce
    (A : WeilDeligneRepresentation.{uK, uG, uV} K S (ν.comp S.subtype)) :
    (induce S A).rank = S.index * A.rank :=
  FiniteRepresentation.rank_induce S A.toFiniteRepresentation

end Langlands.WeilDeligneRepresentation
