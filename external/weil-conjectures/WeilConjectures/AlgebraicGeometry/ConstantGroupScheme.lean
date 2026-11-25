/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Limits
import Mathlib.AlgebraicGeometry.PullbackCarrier

/-!
# Constant group schemes and their points

Source: Stacks Project, Groupoids, Example 39.5.6 (Tag 03YW), and Etale Cohomology,
Remark 59.23.2 (Tag 03P5) (blueprint: def-weil-pbc-constant-group-scheme).
-/

@[expose] public section

universe u v

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

variable (T : Scheme.{u}) (E : Type v) [Small.{u} E] [AddCommGroup E]

/-- (blueprint: def-weil-pbc-constant-group-scheme) The constant scheme over `T` with value
`E` is the coproduct of copies of `T`, indexed by `E` (Stacks, Tag 03YW). -/
noncomputable def constantGroupScheme : Scheme.{u} := ∐ fun _ : E => T

/-- (blueprint: def-weil-pbc-constant-group-scheme) The `e`-th coprojection into the constant
scheme (Stacks, Tag 03YW). -/
noncomputable def constantGroupSchemeIncl (e : E) :
    T ⟶ constantGroupScheme T E := Sigma.ι (fun _ : E => T) e

/-- (blueprint: def-weil-pbc-constant-group-scheme) The codiagonal structure morphism of the
constant `T`-scheme (Stacks, Tag 03YW). -/
noncomputable def constantGroupSchemeProjection : constantGroupScheme T E ⟶ T :=
  Sigma.desc (fun _ : E => 𝟙 T)

/-- (blueprint: def-weil-pbc-constant-group-scheme) The clopen component indexed by `e` is
the image of its coprojection (Stacks, Tag 03YW). -/
noncomputable def constantGroupSchemeComponent (e : E) : Set (constantGroupScheme T E) :=
  Set.range (constantGroupSchemeIncl T E e)

/-- (blueprint: def-weil-pbc-constant-group-scheme) The fibre square of the codiagonal with
itself (Stacks, Tag 03YW). -/
noncomputable def constantGroupSchemeSquare : Scheme.{u} :=
  pullback (constantGroupSchemeProjection T E) (constantGroupSchemeProjection T E)

/-- (blueprint: def-weil-pbc-constant-group-scheme) The part of the fibre square lying over
the `e`-th and `e'`-th components (Stacks, Tag 03YW). -/
noncomputable def constantGroupSchemePairComponent (e e' : E) :
    Set (constantGroupSchemeSquare T E) :=
  {x | (pullback.fst (constantGroupSchemeProjection T E)
      (constantGroupSchemeProjection T E)) x ∈ constantGroupSchemeComponent T E e ∧
    (pullback.snd (constantGroupSchemeProjection T E)
      (constantGroupSchemeProjection T E)) x ∈ constantGroupSchemeComponent T E e'}

/-- (blueprint: def-weil-pbc-constant-group-scheme) The pullback has the base map
`ρ = π ∘ p = π ∘ q` (Stacks, Tag 03YW). -/
noncomputable def constantGroupSchemeSquareProjection : constantGroupSchemeSquare T E ⟶ T :=
  pullback.fst (constantGroupSchemeProjection T E) (constantGroupSchemeProjection T E) ≫
    constantGroupSchemeProjection T E

/-- (blueprint: lem-weil-pbc-constant-group-scheme-multiplication, the existence in (b) and
`π ∘ m = ρ` in (c)) Existence of the componentwise multiplication morphism over `T`
(Stacks, Tag 03YW). The coproduct components form a disjoint
open cover. Pulling it back along both projections covers the fibre square by the pair components.
On overlaps with different indices the domain is empty; on identical overlaps the formulas agree.
Glue the component maps, then compare their composites with each cover map to prove the resulting
morphism lies over `T`. Uniqueness and the remaining component claims belong to the pointer node. -/
theorem exists_constantGroupSchemeMultiplication :
    ∃ m : constantGroupSchemeSquare T E ⟶ constantGroupScheme T E,
      (∀ ij : E × E,
        (Scheme.Pullback.openCoverOfLeftRight
          (sigmaOpenCover (fun _ : E => T)) (sigmaOpenCover (fun _ : E => T))
          (constantGroupSchemeProjection T E) (constantGroupSchemeProjection T E)).f ij ≫ m =
          pullback.fst
            (constantGroupSchemeIncl T E ij.1 ≫ constantGroupSchemeProjection T E)
            (constantGroupSchemeIncl T E ij.2 ≫ constantGroupSchemeProjection T E) ≫
            constantGroupSchemeIncl T E (ij.1 + ij.2)) ∧
      m ≫ constantGroupSchemeProjection T E = constantGroupSchemeSquareProjection T E := by
  classical
  let C := Scheme.Pullback.openCoverOfLeftRight
    (sigmaOpenCover (fun _ : E => T)) (sigmaOpenCover (fun _ : E => T))
    (constantGroupSchemeProjection T E) (constantGroupSchemeProjection T E)
  have hVdisj (e d : E) (h : e ≠ d) :
      Disjoint (constantGroupSchemeComponent T E e)
        (constantGroupSchemeComponent T E d) := by
    rw [Set.disjoint_left]
    rintro x ⟨a, ha⟩ ⟨b, hb⟩
    have he := (sigmaι_eq_iff (fun _ : E => T) e d a b).mp (ha.trans hb.symm)
    exact h (congrArg Sigma.fst he)
  have hWdisj (ij ij' : E × E) (h : ij ≠ ij') :
      Disjoint (constantGroupSchemePairComponent T E ij.1 ij.2)
        (constantGroupSchemePairComponent T E ij'.1 ij'.2) := by
    rw [Set.disjoint_left]
    intro x hx hy
    by_cases h1 : ij.1 = ij'.1
    · have h2 : ij.2 ≠ ij'.2 := fun h2 ↦ h (Prod.ext h1 h2)
      exact Set.disjoint_left.mp (hVdisj _ _ h2) hx.2 hy.2
    · exact Set.disjoint_left.mp (hVdisj _ _ h1) hx.1 hy.1
  have hRange (ij : E × E) :
      Set.range (C.f ij) = constantGroupSchemePairComponent T E ij.1 ij.2 := by
    dsimp only [C]
    rw [Scheme.Pullback.openCoverOfLeftRight_f]
    refine (Scheme.Pullback.range_map
      (f := (sigmaOpenCover (fun _ : E => T)).f ij.1 ≫
        constantGroupSchemeProjection T E)
      (g := (sigmaOpenCover (fun _ : E => T)).f ij.2 ≫
        constantGroupSchemeProjection T E)
      (constantGroupSchemeProjection T E) (constantGroupSchemeProjection T E)
      ((sigmaOpenCover (fun _ : E => T)).f ij.1)
      ((sigmaOpenCover (fun _ : E => T)).f ij.2) (𝟙 T)
      (Category.comp_id _) (Category.comp_id _)).trans ?_
    rfl
  let f := fun ij : E × E ↦ C.f ij ≫ constantGroupSchemeSquareProjection T E ≫
    constantGroupSchemeIncl T E (ij.1 + ij.2)
  have hf : ∀ ij ij', pullback.fst (C.f ij) (C.f ij') ≫ f ij =
      pullback.snd (C.f ij) (C.f ij') ≫ f ij' := by
    intro ij ij'
    by_cases h : ij = ij'
    · subst ij'
      dsimp [f]
      simp only [← Category.assoc, pullback.condition]
    · have : IsEmpty ↥(pullback (C.f ij) (C.f ij')) :=
        Scheme.isEmpty_pullback (C.f ij) (C.f ij')
          (by rw [hRange ij, hRange ij']; exact hWdisj _ _ h)
      exact (isInitialOfIsEmpty).hom_ext _ _
  let m := C.glueMorphisms f hf
  have hm (ij : E × E) : C.f ij ≫ m = f ij := C.ι_glueMorphisms f hf ij
  have hC (ij : E × E) :
      C.f ij ≫ constantGroupSchemeSquareProjection T E =
        pullback.fst (constantGroupSchemeIncl T E ij.1 ≫
          constantGroupSchemeProjection T E)
          (constantGroupSchemeIncl T E ij.2 ≫
            constantGroupSchemeProjection T E) := by
    simp [C, constantGroupSchemeSquareProjection,
      Scheme.Pullback.openCoverOfLeftRight_f, constantGroupSchemeIncl,
      constantGroupSchemeProjection]
    rfl
  refine ⟨m, ?_, ?_⟩
  · intro ij
    rw [hm]
    dsimp [f]
    rw [← Category.assoc, hC]
  · apply C.hom_ext
    intro ij
    rw [← Category.assoc, hm]
    simp [f, constantGroupSchemeIncl, constantGroupSchemeProjection]

/-- (blueprint: def-weil-pbc-constant-group-scheme) Multiplication maps the pair component
indexed by `(e,e')` to the component indexed by `e + e'` (Stacks, Tag 03YW). -/
noncomputable def constantGroupSchemeMultiplication :
    constantGroupSchemeSquare T E ⟶ constantGroupScheme T E :=
  Classical.choose (exists_constantGroupSchemeMultiplication T E)

/-- (blueprint: def-weil-pbc-constant-group-scheme) A point of the constant group scheme over
the `T`-scheme `s : U ⟶ T` is a morphism commuting with the structure maps (Stacks, Tag 03YW). -/
def ConstantGroupSchemePoint {U : Scheme.{u}} (s : U ⟶ T) : Type u :=
  {f : U ⟶ constantGroupScheme T E // f ≫ constantGroupSchemeProjection T E = s}

/-- (blueprint: def-weil-pbc-constant-group-scheme) The sum of two `T`-points is obtained by
their pairing into the fibre square, followed by multiplication (Stacks, Tag 03YW). -/
noncomputable def constantGroupSchemePointAdd {U : Scheme.{u}} (s : U ⟶ T)
    (f g : ConstantGroupSchemePoint T E s) : ConstantGroupSchemePoint T E s :=
  ⟨pullback.lift f.1 g.1 (f.2.trans g.2.symm) ≫
      constantGroupSchemeMultiplication T E,
    by
      rw [Category.assoc, show constantGroupSchemeMultiplication T E ≫
          constantGroupSchemeProjection T E = constantGroupSchemeSquareProjection T E from
          (Classical.choose_spec (exists_constantGroupSchemeMultiplication T E)).2]
      simp only [constantGroupSchemeSquareProjection, pullback.lift_fst_assoc, f.2]⟩

/-- (blueprint: def-weil-pbc-constant-group-scheme) The constant `T`-point attached to `e`
is the coprojection composed with the structure map of `U` (Stacks, Tag 03YW). -/
noncomputable def constantGroupSchemeConstantPoint {U : Scheme.{u}} (s : U ⟶ T) (e : E) :
    ConstantGroupSchemePoint T E s :=
  ⟨s ≫ constantGroupSchemeIncl T E e,
    by simp [constantGroupSchemeIncl, constantGroupSchemeProjection]⟩

/-- (blueprint: def-weil-pbc-constant-group-scheme) The canonical map from `E` to the
`T`-points of the constant group scheme (Stacks, Tag 03YW). -/
noncomputable def constantGroupSchemeCanonicalMap {U : Scheme.{u}} (s : U ⟶ T) :
    E → ConstantGroupSchemePoint T E s :=
  constantGroupSchemeConstantPoint T E s

end AlgebraicGeometry
