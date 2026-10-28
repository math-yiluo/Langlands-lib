import Langlands.Cohomology.DivisibleSystem.HomSystem

/-!
# The complex of compatible families of graded morphisms

Harris, *Galois properties of cohomological automorphic forms on GL(n)*, proof of
Proposition 4.10, pp.311-312, checks a Mittag-Leffler condition, as `m` varies, for the
complexes (4.10.2) and the maps (4.10.3) between them. `DivisibleSystem.HomSystem` gives
the corresponding inverse system for `ℓ`-divisible systems `T` and `W` of cochain
complexes as `homComplexSystem R T W`, `m ↦ Hom^•(T m, W m)`, and
`homComplexLimit R T W` is its limit chosen by `limit`.

This module describes that limit explicitly. In degree `n` it is the `R`-module of
families `z m : Cochain (T m) (W m) n`, one for each `m : ℕ`, with
`cochainTransition h (z m) = z m'` for all `m' ≤ m`; equivalently, with this equation for
all consecutive levels `m ≤ m + 1`. The differential of the Hom complexes is applied
levelwise, which preserves compatible families because the transitions commute with the
differential. The evaluations at the levels `m` are chain maps forming a limit cone over
`homComplexSystem R T W`, which yields the canonical isomorphism with
`homComplexLimit R T W`.

Harris's surjectivity of the maps (4.10.3), the Mittag-Leffler argument, the cohomology
of the limit, Ext groups and the identification of Harris's complexes (4.10.2) with Hom
complexes are not part of this module.
-/

noncomputable section

namespace Langlands.Cohomology

open CategoryTheory CategoryTheory.Limits Opposite
open CochainComplex.HomComplex

universe w v u

namespace DivisibleSystem

section CompatibleHomComplex

variable (R : Type w) [Ring R] {C : Type u} [Category.{v} C] [Abelian C] [Linear R C]
  {ℓ : ℕ} (T W : DivisibleSystem (CochainComplex C ℤ) ℓ)

/-- Degree `n` of the complex of compatible families: the families
`z m : Cochain (T m) (W m) n` with `cochainTransition h (z m) = z m'` for all `m' ≤ m`. -/
def compatibleCochains (n : ℤ) : Submodule R (∀ m : ℕ, Cochain (T.obj m) (W.obj m) n) where
  carrier := {z | ∀ ⦃m' m : ℕ⦄ (h : m' ≤ m), cochainTransition T W h (z m) = z m'}
  add_mem' {z z'} hz hz' m' m h := by
    change cochainTransitionLinear R T W h n (z m + z' m) = z m' + z' m'
    rw [map_add, cochainTransitionLinear_apply, cochainTransitionLinear_apply, hz h, hz' h]
  zero_mem' m' m h := (cochainTransitionLinear R T W h n).map_zero
  smul_mem' r z hz m' m h := by
    change cochainTransitionLinear R T W h n (r • z m) = r • z m'
    rw [map_smul, cochainTransitionLinear_apply, hz h]

lemma mem_compatibleCochains_iff {n : ℤ} (z : ∀ m : ℕ, Cochain (T.obj m) (W.obj m) n) :
    z ∈ compatibleCochains R T W n ↔
      ∀ ⦃m' m : ℕ⦄ (h : m' ≤ m), cochainTransition T W h (z m) = z m' :=
  Iff.rfl

/-- It suffices to check compatibility for consecutive levels `m ≤ m + 1`, i.e. for
the maps (4.10.3). -/
lemma mem_compatibleCochains_iff_succ {n : ℤ}
    (z : ∀ m : ℕ, Cochain (T.obj m) (W.obj m) n) :
    z ∈ compatibleCochains R T W n ↔
      ∀ m : ℕ, cochainTransition T W (Nat.le_succ m) (z (m + 1)) = z m := by
  refine ⟨fun hz m => hz (Nat.le_succ m), fun hz m' m h => ?_⟩
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h
  induction k with
  | zero => exact cochainTransition_refl T W m' (z m')
  | succ k ih =>
    have h₁ : m' ≤ m' + k := Nat.le_add_right m' k
    have h₂ : m' + k ≤ m' + k + 1 := Nat.le_succ (m' + k)
    calc cochainTransition T W h (z (m' + (k + 1)))
        = cochainTransition T W h₁ (cochainTransition T W h₂ (z (m' + k + 1))) :=
          (cochainTransition_trans T W h₁ h₂ _).symm
      _ = cochainTransition T W h₁ (z (m' + k)) := by rw [hz (m' + k)]
      _ = z m' := ih h₁

lemma δ_mem_compatibleCochains (n n' : ℤ) {z : ∀ m : ℕ, Cochain (T.obj m) (W.obj m) n}
    (hz : z ∈ compatibleCochains R T W n) :
    (fun m => δ n n' (z m)) ∈ compatibleCochains R T W n' := fun _ m h =>
  (δ_cochainTransition T W h n n' (z m)).symm.trans (congrArg (δ n n') (hz h))

/-- The differential of the Hom complexes, applied levelwise to compatible families. -/
def compatibleδ (n n' : ℤ) :
    compatibleCochains R T W n →ₗ[R] compatibleCochains R T W n' where
  toFun z := ⟨fun m => δ n n' (z.1 m), δ_mem_compatibleCochains R T W n n' z.2⟩
  map_add' z z' := Subtype.ext (funext fun m => δ_add n n' (z.1 m) (z'.1 m))
  map_smul' r z := Subtype.ext (funext fun m => δ_smul n n' r (z.1 m))

lemma compatibleδ_apply_coe (n n' : ℤ) (z : compatibleCochains R T W n) (m : ℕ) :
    (compatibleδ R T W n n' z).1 m = δ n n' (z.1 m) :=
  rfl

/-- The complex of compatible families of graded morphisms `T m ⟶ W m`, with the
levelwise differential. -/
def compatibleHomComplex : CochainComplex (ModuleCat.{v} R) ℤ where
  X n := ModuleCat.of R (compatibleCochains R T W n)
  d n n' := ModuleCat.ofHom (compatibleδ R T W n n')
  shape n n' hnn' := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro z
    exact Subtype.ext (funext fun m => δ_shape n n' hnn' (z.1 m))
  d_comp_d' i j k _ _ := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro z
    exact Subtype.ext (funext fun m => δ_δ i j k (z.1 m))

/-- Evaluation of a compatible family at level `m`, in degree `n`. -/
def compatibleEvalLinear (m : ℕ) (n : ℤ) :
    compatibleCochains R T W n →ₗ[R] Cochain (T.obj m) (W.obj m) n :=
  (LinearMap.proj m).comp (compatibleCochains R T W n).subtype

/-- Evaluation at level `m`, as a chain map to the Hom complex of level `m`. -/
def compatibleEval (m : ℕ) :
    compatibleHomComplex R T W ⟶ LinearHomComplex.complex R (T.obj m) (W.obj m) where
  f n := ModuleCat.ofHom (compatibleEvalLinear R T W m n)
  comm' n n' _ := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro z
    rfl

lemma compatibleEval_f_apply (m : ℕ) (n : ℤ) (z : compatibleCochains R T W n) :
    (compatibleEval R T W m).f n z = z.1 m :=
  rfl

/-- The cone over `homComplexSystem R T W` given by the evaluations at the levels. -/
@[simps pt]
def compatibleHomComplexCone : Cone (homComplexSystem R T W) where
  pt := compatibleHomComplex R T W
  π :=
    { app m := compatibleEval R T W m.unop
      naturality m m' φ := by
        ext n : 1
        apply ModuleCat.hom_ext
        apply LinearMap.ext
        intro z
        exact (z.2 (leOfHom φ.unop)).symm }

/-- The compatible family given by an element of the apex of a cone over
`homComplexSystem R T W`. -/
@[simps]
def compatibleHomComplexLift (s : Cone (homComplexSystem R T W)) (n : ℤ) :
    s.pt.X n →ₗ[R] compatibleCochains R T W n where
  toFun x := ⟨fun m => (s.π.app (op m)).f n x, fun _ _ h =>
    congrArg (fun g => g.hom x) (HomologicalComplex.congr_hom (s.w (homOfLE h).op) n)⟩
  map_add' x y := Subtype.ext (funext fun m => ((s.π.app (op m)).f n).hom.map_add x y)
  map_smul' r x := Subtype.ext (funext fun m => ((s.π.app (op m)).f n).hom.map_smul r x)

/-- The complex of compatible families is a limit of the inverse system of Hom complexes
`homComplexSystem R T W`, with the evaluations as projections. -/
def compatibleHomComplexIsLimit : IsLimit (compatibleHomComplexCone R T W) where
  lift s :=
    { f n := ModuleCat.ofHom (compatibleHomComplexLift R T W s n)
      comm' n n' _ := by
        apply ModuleCat.hom_ext
        apply LinearMap.ext
        intro x
        exact Subtype.ext (funext fun m =>
          congrArg (fun g => g.hom x) ((s.π.app (op m)).comm n n')) }
  fac s m := by
    ext n : 1
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    rfl
  uniq s g hg := by
    ext n : 1
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    exact Subtype.ext (funext fun m => congrArg (fun k => (k.f n).hom x) (hg (op m)))

/-- The canonical isomorphism between the complex of compatible families and the inverse
limit `homComplexLimit R T W` of the Hom complexes. -/
def compatibleHomComplexIsoLimit : compatibleHomComplex R T W ≅ homComplexLimit R T W :=
  (compatibleHomComplexIsLimit R T W).conePointUniqueUpToIso (limit.isLimit _)

@[reassoc (attr := simp)]
lemma compatibleHomComplexIsoLimit_hom_π (m : ℕ) :
    (compatibleHomComplexIsoLimit R T W).hom ≫ limit.π (homComplexSystem R T W) (op m) =
      compatibleEval R T W m :=
  (compatibleHomComplexIsLimit R T W).conePointUniqueUpToIso_hom_comp (limit.isLimit _) (op m)

@[reassoc (attr := simp)]
lemma compatibleHomComplexIsoLimit_inv_eval (m : ℕ) :
    (compatibleHomComplexIsoLimit R T W).inv ≫ compatibleEval R T W m =
      limit.π (homComplexSystem R T W) (op m) :=
  (compatibleHomComplexIsLimit R T W).conePointUniqueUpToIso_inv_comp (limit.isLimit _) (op m)

end CompatibleHomComplex

end DivisibleSystem

section Smooth

variable (R : Type u) [CommRing R] (G : Type v) [Group G] [TopologicalSpace G] {ℓ : ℕ}

/-- The complex of compatible families of graded equivariant maps for `ℓ`-divisible
systems of cochain complexes of smooth representations; it is a limit of
`smoothHomComplexSystem R G T W`. -/
abbrev smoothCompatibleHomComplex (T W : SmoothRepComplexDivisibleSystem.{v, u, w} R G ℓ) :
    CochainComplex (ModuleCat.{w} R) ℤ :=
  DivisibleSystem.compatibleHomComplex R T W

end Smooth

end Langlands.Cohomology
