import Langlands.Algebra.NonUnitalModule
import Mathlib.Algebra.DirectSum.Basic
import Mathlib.CategoryTheory.Limits.Shapes.Products

/-!
# Actual finite-support direct sums of original nonunital modules

The ambient direct sum has its coordinatewise original action. A finite common
idempotent proves nondegeneracy and yields the actual coproduct cofan.
-/

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace Langlands.Algebra.NonUnitalModuleDirectSum

universe uA uI uM uN

variable {A : Type uA} [NonUnitalRing A] {I : Type uI}
variable (M : I → Type uM) [∀ i, AddCommGroup (M i)] [∀ i, NonUnitalModule A (M i)]

local instance : DecidableEq I := Classical.decEq I

/-- The ordinary additive direct sum, with its actual finitely supported carrier. -/
abbrev Carrier := Π₀ i, M i

/-- Act on every coordinate using precisely its original action. -/
instance action : NonUnitalModule A (Carrier M) where
  smul a x := DFinsupp.mapRange (fun _ m => a • m) (fun _ => smul_zero a) x
  smul_zero a := DFinsupp.ext fun _ => smul_zero a
  smul_add a x y := DFinsupp.ext fun i => smul_add a (x i) (y i)
  mul_smul a b x := DFinsupp.ext fun i => mul_smul a b (x i)
  add_smul a b x := DFinsupp.ext fun i => NonUnitalModule.add_smul a b (x i)
  zero_smul x := DFinsupp.ext fun i => NonUnitalModule.zero_smul (x i)

@[simp] theorem smul_apply (a : A) (x : Carrier M) (i : I) :
    (a • x) i = a • x i := rfl

@[simp] theorem smul_single (a : A) (i : I) (m : M i) :
    a • (DFinsupp.single i m : Carrier M) = DFinsupp.single i (a • m) := by
  classical
  exact DFinsupp.mapRange_single

/-- The original summand injection is an additive intertwiner. -/
def inclusion (i : I) : NonUnitalModuleHom A (M i) (Carrier M) := by
  classical
  exact
    { toAddMonoidHom := DFinsupp.singleAddHom M i
      map_smul' := fun a m => (smul_single M a i m).symm }

@[simp] theorem inclusion_apply (i : I) (m : M i) :
    inclusion (A := A) M i m = DFinsupp.single i m := rfl

variable {N : Type uN} [AddCommGroup N] [NonUnitalModule A N]

/-- Assemble original intertwiners by the finite-support sum formula. -/
def desc (f : ∀ i, NonUnitalModuleHom A (M i) N) :
    NonUnitalModuleHom A (Carrier M) N := by
  classical
  let g : Carrier M →+ N := DirectSum.toAddMonoid (fun i => (f i).toAddMonoidHom)
  refine { toAddMonoidHom := g, map_smul' := ?_ }
  intro a x
  refine DirectSum.induction_on x ?_ ?_ ?_
  · rw [smul_zero, g.map_zero, smul_zero]
  · intro i m
    change g (a • (DFinsupp.single i m : Carrier M)) = a • g (DFinsupp.single i m)
    rw [smul_single]
    change DirectSum.toAddMonoid (fun j => (f j).toAddMonoidHom)
        (DirectSum.of M i (a • m)) =
      a • DirectSum.toAddMonoid (fun j => (f j).toAddMonoidHom) (DirectSum.of M i m)
    rw [DirectSum.toAddMonoid_of, DirectSum.toAddMonoid_of]
    exact (f i).map_smul a m
  · intro x y hx hy
    rw [smul_add, g.map_add, hx, hy, g.map_add, smul_add]

@[simp] theorem desc_inclusion (f : ∀ i, NonUnitalModuleHom A (M i) N)
    (i : I) (m : M i) : desc M f (inclusion (A := A) M i m) = f i m := by
  classical
  exact DirectSum.toAddMonoid_of _ i m

/-- Original maps out of the direct sum are determined on the summands. -/
theorem hom_ext {f g : NonUnitalModuleHom A (Carrier M) N}
    (h : ∀ i m, f (inclusion (A := A) M i m) = g (inclusion (A := A) M i m)) :
    f = g := by
  classical
  have hfg : f.toAddMonoidHom = g.toAddMonoidHom :=
    DFinsupp.addHom_ext h
  exact NonUnitalModuleHom.ext (DFunLike.congr_fun hfg)

/-- Every finite-support vector is fixed by a common upper idempotent. -/
theorem isNondegenerate (hA : IsIdempotented A) (hM : ∀ i, IsNondegenerate A (M i)) :
    IsNondegenerate A (Carrier M) := by
  classical
  intro x
  refine DirectSum.induction_on x ?_ ?_ ?_
  · exact ⟨⟨0, IsIdempotentElem.zero⟩, smul_zero (0 : A)⟩
  · intro i m
    obtain ⟨e, he⟩ := hM i m
    refine ⟨e, ?_⟩
    change (e : A) • (DFinsupp.single i m : Carrier M) = DFinsupp.single i m
    rw [smul_single, he]
  · rintro x y ⟨e, he⟩ ⟨f, hf⟩
    obtain ⟨g, hg⟩ := hA.finite_upper_bound {e, f}
    refine ⟨g, ?_⟩
    rw [smul_add, Idempotent.smul_eq_of_le (hg e (by simp)) he,
      Idempotent.smul_eq_of_le (hg f (by simp)) hf]

/-- The direct sum object, in a universe large enough for its index type. -/
def object (hA : IsIdempotented A)
    (P : I → NondegenerateModuleCat.{uA, max uI uM} A) :
    NondegenerateModuleCat.{uA, max uI uM} A :=
  ⟨NonUnitalModuleCat.of A (Carrier (fun i => (P i).obj)),
    isNondegenerate _ hA (fun i => (P i).property)⟩

/-- The actual cofan retains the original singleton inclusions. -/
def cofan (hA : IsIdempotented A)
    (P : I → NondegenerateModuleCat.{uA, max uI uM} A) : Cofan P :=
  Cofan.mk (object hA P) (fun i => ObjectProperty.homMk (inclusion (fun j => (P j).obj) i))

/-- The finite-support cofan has the full categorical coproduct property. -/
def cofanIsColimit (hA : IsIdempotented A)
    (P : I → NondegenerateModuleCat.{uA, max uI uM} A) : IsColimit (cofan hA P) := by
  refine Cofan.IsColimit.mk _
    (fun s => ObjectProperty.homMk (desc (fun i => (P i).obj) (fun i => (s.inj i).hom)))
    ?_ ?_
  · intro s i
    apply ObjectProperty.hom_ext
    apply NonUnitalModuleHom.ext
    intro m
    exact desc_inclusion (fun j => (P j).obj) (fun j => (s.inj j).hom) i m
  · intro s m hm
    apply ObjectProperty.hom_ext
    apply hom_ext (fun i => (P i).obj)
    intro i x
    have hx := congrArg (fun k => k.hom.toAddMonoidHom x) (hm i)
    exact hx.trans (desc_inclusion (fun j => (P j).obj)
      (fun j => (s.inj j).hom) i x).symm

/-! The action and universal-property interfaces preserve independent universes. -/

example : {A : Type uA} → [NonUnitalRing A] → {I : Type uI} →
    (M : I → Type uM) → [∀ i, AddCommGroup (M i)] →
    [∀ i, NonUnitalModule A (M i)] → NonUnitalModule A (Carrier M) :=
  @action.{uA, uI, uM}

example : {A : Type uA} → [NonUnitalRing A] → (hA : IsIdempotented A) →
    {I : Type uI} → (P : I → NondegenerateModuleCat.{uA, max uI uM} A) →
    IsColimit (cofan hA P) :=
  fun {_} _ hA {_} P => cofanIsColimit hA P

end Langlands.Algebra.NonUnitalModuleDirectSum
