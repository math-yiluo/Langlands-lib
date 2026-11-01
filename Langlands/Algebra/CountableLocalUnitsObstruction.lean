import Langlands.Algebra.NonUnitalModuleFree
import Langlands.Algebra.NondegenerateModuleExactnessConcrete
import Langlands.CategoryTheory.Renard.HomExactnessComparison
import Mathlib.Data.Set.Countable

set_option autoImplicit false

noncomputable section

open CategoryTheory
open scoped BigOperators

namespace Langlands.Algebra.CountableLocalUnitsObstruction

universe uA uI uM uL

variable {A : Type uA} [NonUnitalRing A]

local instance : NonUnitalModule A A := NonUnitalModule.regular A

/-- Countable right local units force every regular-source map into a sum to use finitely many coordinates. -/
theorem finite_image_support
    (hcount : ∀ a : ℕ → A, ∃ e : A, ∀ n, a n * e = a n)
    {I : Type uI} (M : I → Type uM)
    [∀ i, AddCommGroup (M i)] [∀ i, NonUnitalModule A (M i)]
    (f : NonUnitalModuleHom A A (NonUnitalModuleDirectSum.Carrier M)) :
    Set.Finite {i : I | ∃ a : A, f a i ≠ 0} := by
  classical
  by_contra hinf
  let S : Set I := {i | ∃ a : A, f a i ≠ 0}
  let j : ℕ ↪ S := Set.Infinite.natEmbedding S hinf
  choose a ha using (fun n : ℕ => (j n).property)
  obtain ⟨e, he⟩ := hcount a
  have hmem (n : ℕ) : f e (j n).val ≠ 0 := by
    intro hzero
    apply ha n
    have hfa : f (a n) = a n • f e := by
      calc
        f (a n) = f (a n * e) := congrArg f (he n).symm
        _ = a n • f e := f.map_smul (a n) e
    rw [hfa]
    change a n • (f e (j n).val) = 0
    rw [hzero, smul_zero]
  have hsub : Set.range (fun n : ℕ => (j n).val) ⊆ {i | f e i ≠ 0} := by
    rintro _ ⟨n, rfl⟩
    exact hmem n
  exact (Set.infinite_range_of_injective (Subtype.val_injective.comp j.injective))
    ((DFinsupp.finite_support (f e)).subset hsub)

/-- Projectivity of the lifted original regular object forces a global right identity. -/
theorem right_identity_of_regular_projective
    (hA : IsIdempotented A)
    (hcount : ∀ a : ℕ → A, ∃ e : A, ∀ n, a n * e = a n)
    (hproj : Projective (NonUnitalModuleFree.regularObject.{uA, uL} hA)) :
    ∃ e : A, ∀ a : A, a * e = a := by
  classical
  let M := NonUnitalModuleFree.regularObject.{uA, uL} hA
  let F := NonUnitalModuleFree.object.{uA, uL, max uA uL} hA M.obj
  let q : F ⟶ M := ObjectProperty.homMk
    (NonUnitalModuleFree.fromFamily (fun m : M.obj => m))
  have hsurj : Function.Surjective q.hom.toAddMonoidHom := by
    intro m
    obtain ⟨e, he⟩ := M.property m
    refine ⟨NonUnitalModuleFree.inclusion M.obj m (ULift.up (e : A)), ?_⟩
    exact (NonUnitalModuleFree.fromFamily_single (fun n : M.obj => n) m (e : A)).trans he
  let : Epi q := (NondegenerateModuleExactnessConcrete.epi_iff hA q).mpr hsurj
  let : Projective M := hproj
  let s : M ⟶ F := Projective.factorThru (𝟙 M) q
  have hsec : s ≫ q = 𝟙 M := Projective.factorThru_comp (𝟙 M) q
  let f : NonUnitalModuleHom A A
      (NonUnitalModuleFree.Carrier.{uA, uL, max uA uL} A M.obj) :=
    s.hom.comp (NonUnitalModuleFree.regularUp.{uA, uL} (A := A))
  have hfinite : Set.Finite {i : M.obj | ∃ a : A, f a i ≠ 0} :=
    finite_image_support hcount (fun _ : M.obj => NonUnitalModuleFree.Regular.{uA, uL} A) f
  let T : Set M.obj := {i | ∃ a : A, f a i ≠ 0}
  let t : Finset M.obj := hfinite.toFinset
  obtain ⟨e, he⟩ := (IsIdempotented.iff_two_sided_local_units.mp hA)
    (t.image (fun i : M.obj => i.down))
  refine ⟨(e : A), fun a => ?_⟩
  let x : NonUnitalModuleFree.Carrier.{uA, uL, max uA uL} A M.obj :=
    s.hom.toAddMonoidHom (ULift.up a)
  let qd : NonUnitalModuleFree.Carrier.{uA, uL, max uA uL} A M.obj →+ A :=
    (NonUnitalModuleFree.regularDown.{uA, uL} (A := A)).toAddMonoidHom.comp
      q.hom.toAddMonoidHom
  have hqd (i : M.obj) (v : NonUnitalModuleFree.Regular.{uA, uL} A) :
      qd (DirectSum.of (fun _ : M.obj => NonUnitalModuleFree.Regular.{uA, uL} A) i v) =
        v.down * i.down := by
    exact congrArg ULift.down
      (NonUnitalModuleFree.fromFamily_single (fun n : M.obj => n) i v.down)
  have hsum : qd x = ∑ i ∈ x.support, (x i).down * i.down := by
    calc
      qd x = qd (∑ i ∈ x.support,
          DirectSum.of (fun _ : M.obj => NonUnitalModuleFree.Regular.{uA, uL} A) i (x i)) :=
        congrArg qd (DirectSum.sum_support_of x).symm
      _ = ∑ i ∈ x.support, (x i).down * i.down := by
        rw [map_sum]
        exact Finset.sum_congr rfl (fun i _ => hqd i (x i))
  have hqx : qd x = a := by
    exact congrArg (fun k : M ⟶ M => (k.hom.toAddMonoidHom (ULift.up a)).down) hsec
  rw [← hqx, hsum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i hi
  have hiT : i ∈ T := ⟨a, (DFinsupp.mem_support_iff.mp hi)⟩
  have hit : i ∈ t := hfinite.mem_toFinset.mpr hiT
  have hier : i.down * (e : A) = i.down :=
    (he i.down (Finset.mem_image.mpr ⟨i, hit, rfl⟩)).2
  rw [mul_assoc, hier]

/-- A ring with countable right local units and no global right identity has nonprojective regular module. -/
theorem regular_not_projective
    (hA : IsIdempotented A)
    (hcount : ∀ a : ℕ → A, ∃ e : A, ∀ n, a n * e = a n)
    (hno : ¬ ∃ e : A, ∀ a : A, a * e = a) :
    ¬ Projective (NonUnitalModuleFree.regularObject.{uA, uL} hA) :=
  fun hp => hno (right_identity_of_regular_projective hA hcount hp)

/-- The singleton sum has the actual regular object as its sole original coordinate. -/
def regularSingleIso (hA : IsIdempotented A) (I : Type (max uA uL)) [Unique I] :
    NonUnitalModuleFree.regularObject.{uA, uL} hA ≅
      NonUnitalModuleFree.object.{uA, uL, max uA uL} hA I := by
  classical
  let f : NonUnitalModuleHom A (NonUnitalModuleFree.Regular.{uA, uL} A)
      (NonUnitalModuleFree.Carrier.{uA, uL, max uA uL} A I) :=
    NonUnitalModuleFree.inclusion I default
  let g : NonUnitalModuleHom A
      (NonUnitalModuleFree.Carrier.{uA, uL, max uA uL} A I)
      (NonUnitalModuleFree.Regular.{uA, uL} A) :=
    { toAddMonoidHom := DFinsupp.evalAddMonoidHom default
      map_smul' := fun _ _ => rfl }
  have hfg : g.comp f = NonUnitalModuleHom.id A (NonUnitalModuleFree.Regular.{uA, uL} A) := by
    apply NonUnitalModuleHom.ext
    intro m
    change g (f m) = m
    simp [f, g, DFinsupp.evalAddMonoidHom]
  have hgf : f.comp g =
      NonUnitalModuleHom.id A (NonUnitalModuleFree.Carrier.{uA, uL, max uA uL} A I) := by
    apply NonUnitalModuleHom.ext
    intro x
    change f (g x) = x
    apply DFinsupp.ext
    intro i
    have hi : i = default := Subsingleton.elim _ _
    subst i
    simp [f, g, DFinsupp.evalAddMonoidHom]
  exact
    { hom := ObjectProperty.homMk f
      inv := ObjectProperty.homMk g
      hom_inv_id := by apply ObjectProperty.hom_ext; exact hfg
      inv_hom_id := by apply ObjectProperty.hom_ext; exact hgf }

/-- A single original regular copy is free in Renard's exact definition. -/
theorem regular_isFree (hA : IsIdempotented A) :
    NonUnitalModuleFree.IsFree.{uA, uL} hA
      (NonUnitalModuleFree.regularObject.{uA, uL} hA) :=
  ⟨PUnit.{max uA uL + 1}, ⟨regularSingleIso hA PUnit⟩⟩

end Langlands.Algebra.CountableLocalUnitsObstruction
