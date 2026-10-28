import Langlands.Cohomology.DivisibleSystem.HomSystem
import Mathlib.Algebra.Homology.HomologicalComplexLimits
import Mathlib.CategoryTheory.CofilteredSystem
import Mathlib.CategoryTheory.Limits.ConcreteCategory.Basic
import Mathlib.CategoryTheory.Preadditive.Projective.Basic

/-!
# Surjectivity of the Hom transitions of `ℓ`-divisible systems

Harris, *Galois properties of cohomological automorphic forms on GL(n)*, proof of
Proposition 4.10, p.312: the maps `C^j_{m+1}(ẽ)^{H_p} ⟶ C^j_m(ẽ)^{H_p}` are surjective, and
since `C^j_m(ẽ)^{H_p}` and `Hom(𝒪_m[C_p/H_p]^M, 𝓛_m)` are free `𝒪/ℓ^m 𝒪[S(ẽ)/H_p]`-modules,
the maps (4.10.3) `T_{m+1}(j, ẽ) ⟶ T_m(j, ẽ)` are surjective. Harris uses this to check the
Mittag-Leffler condition for the complexes (4.10.2).

For `ℓ`-divisible systems `T` and `W` in an `R`-linear abelian category, this module proves
the corresponding surjectivity for the transitions `homTransition` of the published inverse
system `homSystem R T W` of the modules `Hom(T m, W m)`. The hypothesis is that `T m` is
projective relative to objects killed by `ℓ ^ m` (`PowTorsionProjective`); for instance a
projective object, or a free `R/ℓ^m R`-module in a category of `R`-modules. The projections
of `W` are epimorphisms for every `ℓ`-divisible system, and no hypothesis on `W` is needed.
The inverse system `homSystem R T W` then satisfies the Mittag-Leffler condition, and every
morphism `T m ⟶ W m` is the level-`m` component of a morphism of the inverse systems
`T.tower ⟶ W.tower`. The same holds degreewise for the inverse system of Hom complexes
`homComplexSystem R T W` of `ℓ`-divisible systems of cochain complexes, in the form of the
hypotheses of the inverse-limit statements of `Langlands.Cohomology.InverseLimit.Statement`.

The identification of Harris's modules `T_m(j, ẽ)` and complexes (4.10.2) with these Hom
systems, and the projectivity of Harris's modules `C^j_m(ẽ)^{H_p}`, are not formalized here.
-/

noncomputable section

namespace Langlands.Cohomology

open CategoryTheory CategoryTheory.Limits Opposite
open CochainComplex.HomComplex

universe w v u

section SequentialLimit

variable {F : ℕᵒᵖ ⥤ Type w}

/-- A family of elements `s j` of `F (op j)` compatible along the maps
`F (op (j + 1)) ⟶ F (op j)` is a section of `F`. -/
lemma mem_sections_of_map_succ (s : ∀ j : ℕ, F.obj (op j))
    (hs : ∀ j, F.map (homOfLE (Nat.le_succ j)).op (s (j + 1)) = s j) :
    (fun j : ℕᵒᵖ => s j.unop) ∈ F.sections := by
  have key : ∀ b k, F.map (homOfLE (Nat.le_add_right b k)).op (s (b + k)) = s b := by
    intro b k
    induction k with
    | zero =>
      change F.map (𝟙 (op b)) (s b) = s b
      rw [CategoryTheory.Functor.map_id]
      rfl
    | succ k ih =>
      change F.map ((homOfLE (Nat.le_succ (b + k))).op ≫ (homOfLE (Nat.le_add_right b k)).op)
        (s (b + k + 1)) = s b
      rw [Functor.map_comp, types_comp_apply, hs, ih]
  rintro ⟨a⟩ ⟨b⟩ f
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le (leOfHom f.unop)
  have hf : f = (homOfLE (Nat.le_add_right b k)).op := Quiver.Hom.unop_inj (Subsingleton.elim _ _)
  subst hf
  exact key b k

variable (hF : ∀ k, Function.Surjective (F.map (homOfLE (Nat.le_succ k)).op))

/-- Successive preimages of `x : F (op n)`: the element of `F (op (n + k))` obtained by
choosing preimages along the surjections `F (op (n + k + 1)) ⟶ F (op (n + k))`. -/
def sequencePreimage {n : ℕ} (x : F.obj (op n)) : (k : ℕ) → F.obj (op (n + k))
  | 0 => x
  | k + 1 => (hF (n + k) (sequencePreimage x k)).choose

lemma map_sequencePreimage_succ {n : ℕ} (x : F.obj (op n)) (k : ℕ) :
    F.map (homOfLE (Nat.le_succ (n + k))).op (sequencePreimage hF x (k + 1)) =
      sequencePreimage hF x k :=
  (hF (n + k) (sequencePreimage hF x k)).choose_spec

lemma map_sequencePreimage {n : ℕ} (x : F.obj (op n)) (k : ℕ) :
    F.map (homOfLE (Nat.le_add_right n k)).op (sequencePreimage hF x k) = x := by
  induction k with
  | zero =>
    change F.map (𝟙 (op n)) x = x
    rw [CategoryTheory.Functor.map_id]
    rfl
  | succ k ih =>
    change F.map ((homOfLE (Nat.le_succ (n + k))).op ≫ (homOfLE (Nat.le_add_right n k)).op)
      (sequencePreimage hF x (k + 1)) = x
    rw [Functor.map_comp, types_comp_apply, map_sequencePreimage_succ, ih]

/-- The section of `F` through `x : F (op n)`: its value at `j` is the image of
`sequencePreimage hF x j : F (op (n + j))` in `F (op j)`. -/
def sequenceSection {n : ℕ} (x : F.obj (op n)) (j : ℕ) : F.obj (op j) :=
  F.map (homOfLE (Nat.le_add_left j n)).op (sequencePreimage hF x j)

lemma map_sequenceSection_succ {n : ℕ} (x : F.obj (op n)) (j : ℕ) :
    F.map (homOfLE (Nat.le_succ j)).op (sequenceSection hF x (j + 1)) =
      sequenceSection hF x j := by
  change (F.map (homOfLE (Nat.le_add_left (j + 1) n)).op ≫ F.map (homOfLE (Nat.le_succ j)).op)
    (sequencePreimage hF x (j + 1)) = _
  rw [← Functor.map_comp]
  change F.map ((homOfLE (Nat.le_succ (n + j))).op ≫ (homOfLE (Nat.le_add_left j n)).op)
    (sequencePreimage hF x (j + 1)) = _
  rw [Functor.map_comp, types_comp_apply, map_sequencePreimage_succ]
  rfl

lemma sequenceSection_self {n : ℕ} (x : F.obj (op n)) : sequenceSection hF x n = x :=
  map_sequencePreimage hF x n

include hF in
/-- If the maps `F (op (k + 1)) ⟶ F (op k)` are surjective, every element of every
`F (op n)` is the value at `n` of a section of `F`. -/
lemma exists_mem_sections_of_surjective_map (n : ℕ) (x : F.obj (op n)) :
    ∃ s ∈ F.sections, s (op n) = x :=
  ⟨fun j => sequenceSection hF x j.unop,
    mem_sections_of_map_succ _ (map_sequenceSection_succ hF x), sequenceSection_self hF x⟩

include hF in
/-- Given surjections `⋯ ⟶ X (n + 1) ⟶ X n ⟶ ⋯ ⟶ X 0` of types, every projection
`lim X ⟶ X n` of a limit cone is surjective (Mathlib's
`Types.surjective_π_app_zero_of_surjective_map` is the case `n = 0`). -/
lemma types_surjective_π_app_of_surjective_map {c : Cone F} (hc : IsLimit c) (n : ℕ) :
    Function.Surjective (c.π.app (op n)) := by
  intro x
  obtain ⟨s, hs, rfl⟩ := exists_mem_sections_of_surjective_map hF n x
  exact ⟨(Types.isLimitEquivSections hc).symm ⟨s, hs⟩,
    Types.isLimitEquivSections_symm_apply hc ⟨s, hs⟩ (op n)⟩

end SequentialLimit

/-- Given surjections `⋯ ⟶ X (n + 1) ⟶ X n ⟶ ⋯ ⟶ X 0` in a concrete category whose
forgetful functor preserves sequential limits, every projection `lim X ⟶ X n` of a limit
cone is surjective (Mathlib's `Concrete.surjective_π_app_zero_of_surjective_map` is the case
`n = 0`). -/
lemma concrete_surjective_π_app_of_surjective_map {C : Type u} [Category.{v} C]
    {FC : C → C → Type*} {CC : C → Type v} [∀ X Y, FunLike (FC X Y) (CC X) (CC Y)]
    [ConcreteCategory.{v} C FC] [PreservesLimitsOfShape ℕᵒᵖ (forget C)] {F : ℕᵒᵖ ⥤ C}
    {c : Cone F} (hc : IsLimit c)
    (hF : ∀ k, Function.Surjective (F.map (homOfLE (Nat.le_succ k)).op)) (n : ℕ) :
    Function.Surjective (c.π.app (op n)) :=
  types_surjective_π_app_of_surjective_map hF (isLimitOfPreserves (forget C) hc) n

namespace DivisibleSystem

section Projective

variable {C : Type u} [Category.{v} C] [Preadditive C]

/-- `P` is projective relative to objects killed by `ℓ ^ m`: every morphism from `P` to the
target of an epimorphism `p : X ⟶ Y` whose source `X` is killed by `ℓ ^ m` lifts along `p`.
In a category of modules over a group ring, free `𝒪/ℓ^m 𝒪[Γ]`-modules have this property;
Harris 1999, p.312, uses the freeness of the modules `C^j_m(ẽ)^{H_p}` over
`𝒪/ℓ^m 𝒪[S(ẽ)/H_p]` for the surjectivity of the maps (4.10.3). -/
def PowTorsionProjective (ℓ m : ℕ) (P : C) : Prop :=
  ∀ ⦃X Y : C⦄ (p : X ⟶ Y), Epi p → powSMul ℓ m X = 0 →
    ∀ g : P ⟶ Y, ∃ f : P ⟶ X, f ≫ p = g

/-- A projective object is projective relative to objects killed by `ℓ ^ m`. -/
lemma powTorsionProjective_of_projective (ℓ m : ℕ) (P : C) [Projective P] :
    PowTorsionProjective ℓ m P := by
  intro X Y p hp _ g
  exact Projective.factors g p

end Projective

section HomSystem

variable (R : Type w) [Ring R] {C : Type u} [Category.{v} C] [Abelian C] [Linear R C]
  {ℓ : ℕ} (T W : DivisibleSystem C ℓ)

/-- Harris 1999, p.312: the transition (4.10.3) `Hom(T m, W m) ⟶ Hom(T m', W m')` is
surjective when `T m` is projective relative to objects killed by `ℓ ^ m`. A morphism
`g : T m' ⟶ W m'` is reached by a lift of `T m ⟶ T m' ⟶ W m'` along the projection
`W m ⟶ W m'`, which is an epimorphism with source killed by `ℓ ^ m`. -/
lemma homTransition_surjective {m' m : ℕ} (h : m' ≤ m)
    (hT : PowTorsionProjective ℓ m (T.obj m)) :
    Function.Surjective (homTransition T W h) := by
  intro g
  obtain ⟨f, hf⟩ := hT (W.projection h) (W.epi_projection h) (W.powSMul_eq_zero m)
    (T.projection h ≫ g)
  exact ⟨f, (homTransition_eq_iff T W h f g).2 hf.symm⟩

/-- The maps of the inverse system `homSystem R T W` are surjective when every `T m` is
projective relative to objects killed by `ℓ ^ m`. -/
lemma homSystem_map_surjective (hT : ∀ m, PowTorsionProjective ℓ m (T.obj m))
    {m m' : ℕᵒᵖ} (φ : m ⟶ m') : Function.Surjective ((homSystem R T W).map φ) :=
  homTransition_surjective T W (leOfHom φ.unop) (hT m.unop)

/-- The inverse system `homSystem R T W` satisfies the Mittag-Leffler condition when every
`T m` is projective relative to objects killed by `ℓ ^ m`. -/
lemma isMittagLeffler_homSystem (hT : ∀ m, PowTorsionProjective ℓ m (T.obj m)) :
    (homSystem R T W ⋙ CategoryTheory.forget (ModuleCat.{v} R)).IsMittagLeffler :=
  Functor.isMittagLeffler_of_surjective _ fun _ _ φ => homSystem_map_surjective R T W hT φ

/-- Every morphism `T n ⟶ W n` is the level-`n` component of a morphism of the inverse
systems `T.tower ⟶ W.tower`, when every `T m` is projective relative to objects killed by
`ℓ ^ m`. -/
lemma towerHomEval_surjective (hT : ∀ m, PowTorsionProjective ℓ m (T.obj m)) (n : ℕ) :
    Function.Surjective (towerHomEval R T W n) :=
  concrete_surjective_π_app_of_surjective_map (homSystemIsLimit R T W)
    (fun k => homSystem_map_surjective R T W hT (homOfLE (Nat.le_succ k)).op) n

end HomSystem

section HomComplexSystem

variable (R : Type w) [Ring R] {C : Type u} [Category.{v} C] [Abelian C] [Linear R C]
  {ℓ : ℕ} (T W : DivisibleSystem (CochainComplex C ℤ) ℓ)

/-- The transition of graded morphisms of degree `n` from level `m` to level `m'` is
surjective when every term `(T m) ^ p` is projective relative to objects killed by
`ℓ ^ m`: each component is lifted by `homTransition_surjective`. -/
lemma cochainTransition_surjective {m' m : ℕ} (h : m' ≤ m)
    (hT : ∀ p, PowTorsionProjective ℓ m ((T.obj m).X p)) (n : ℤ) :
    Function.Surjective (cochainTransition T W h (n := n)) := by
  intro z'
  refine ⟨Cochain.mk fun p q hpq =>
    (homTransition_surjective (T.degree p) (W.degree q) h (hT p) (z'.v p q hpq)).choose, ?_⟩
  ext p q hpq
  rw [cochainTransition_v]
  exact (homTransition_surjective (T.degree p) (W.degree q) h (hT p) (z'.v p q hpq)).choose_spec

/-- The degree-`n` components of the maps of the inverse system of Hom complexes
`homComplexSystem R T W` are surjective when every term `(T m) ^ p` is projective relative
to objects killed by `ℓ ^ m`. -/
lemma homComplexSystem_map_f_surjective (hT : ∀ m p, PowTorsionProjective ℓ m ((T.obj m).X p))
    {m m' : ℕᵒᵖ} (φ : m ⟶ m') (n : ℤ) :
    Function.Surjective (((homComplexSystem R T W).map φ).f n) :=
  cochainTransition_surjective T W (leOfHom φ.unop) (hT m.unop) n

/-- Harris 1999, proof of Proposition 4.10: the inverse system of Hom complexes
`homComplexSystem R T W` satisfies the Mittag-Leffler condition in every degree when every
term `(T m) ^ p` is projective relative to objects killed by `ℓ ^ m`. This is the
degreewise hypothesis of `DegreewiseInverseLimitCohomologyStatement`. -/
lemma isMittagLeffler_homComplexSystem_eval
    (hT : ∀ m p, PowTorsionProjective ℓ m ((T.obj m).X p)) (n : ℤ) :
    (homComplexSystem R T W ⋙ HomologicalComplex.eval (ModuleCat.{v} R) (ComplexShape.up ℤ) n ⋙
      CategoryTheory.forget (ModuleCat.{v} R)).IsMittagLeffler :=
  Functor.isMittagLeffler_of_surjective _ fun _ _ φ =>
    homComplexSystem_map_f_surjective R T W hT φ n

/-- The degree-`n` components of the limit projections `homComplexLimit R T W ⟶ Hom^•(T m, W m)`
are surjective when every term `(T m) ^ p` is projective relative to objects killed by
`ℓ ^ m`. -/
lemma homComplexLimit_π_f_surjective (hT : ∀ m p, PowTorsionProjective ℓ m ((T.obj m).X p))
    (m : ℕ) (n : ℤ) :
    Function.Surjective ((limit.π (homComplexSystem R T W) (op m)).f n) :=
  concrete_surjective_π_app_of_surjective_map
    (isLimitOfPreserves (HomologicalComplex.eval (ModuleCat.{v} R) (ComplexShape.up ℤ) n)
      (limit.isLimit (homComplexSystem R T W)))
    (fun k => homComplexSystem_map_f_surjective R T W hT (homOfLE (Nat.le_succ k)).op n) m

end HomComplexSystem

end DivisibleSystem

section Smooth

variable (R : Type u) [CommRing R] (G : Type v) [Group G] [TopologicalSpace G] {ℓ : ℕ}

/-- Harris 1999, proof of Proposition 4.10, for `ℓ`-divisible systems of cochain complexes
of smooth representations: the inverse system of Hom complexes of equivariant maps satisfies
the Mittag-Leffler condition in every degree when every term `(T m) ^ p` is projective,
in the category of smooth representations, relative to objects killed by `ℓ ^ m`. -/
lemma isMittagLeffler_smoothHomComplexSystem_eval
    (T W : SmoothRepComplexDivisibleSystem.{v, u, w} R G ℓ)
    (hT : ∀ m p, DivisibleSystem.PowTorsionProjective ℓ m ((T.obj m).X p)) (n : ℤ) :
    (smoothHomComplexSystem R G T W ⋙
      HomologicalComplex.eval (ModuleCat.{w} R) (ComplexShape.up ℤ) n ⋙
        forget (ModuleCat.{w} R)).IsMittagLeffler :=
  DivisibleSystem.isMittagLeffler_homComplexSystem_eval R T W hT n

end Smooth

end Langlands.Cohomology
