/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Adjunction.PartialAdjoint
public import Mathlib.CategoryTheory.Adjunction.Mates
public import Mathlib.CategoryTheory.HomCongr
public import Mathlib.CategoryTheory.Triangulated.Functor
public import WeilConjectures.Mathlib.CategoryTheory.Triangulated.Pretriangulated

/-!
# The right adjoint of the closed part of a recollement

Let `C` be a pretriangulated category, `i : Z ⥤ C` a fully faithful functor (the direct image
along a closed immersion), and `j^* ⊣ j_*` an adjunction `C ⇄ U` with invertible counit (the
pullback to and the direct image from the open complement), `j^*` being triangulated. Assume
that `j^* i = 0` and that every object killed by `j^*` lies in the essential image of `i`.

Then for every `K` the fibre of the unit `K ⟶ j_* j^* K` lies in the essential image of `i`,
`Hom((i M)⟦n⟧, j_* N) = 0`, and consequently `i` has a right adjoint `i^!`, with which the
counit of `i ⊣ i^!` and the unit of `j^* ⊣ j_*` extend to a distinguished triangle

`i i^! K ⟶ K ⟶ j_* j^* K ⟶ (i i^! K)⟦1⟧`

whose third map is unique; moreover `i^! j_* = 0`. This is the formal part of the supported
localization triangle (blueprint `lemma-local-cohomology-right-adjoint--2`):
it gives the right adjoint `Ri^!` of `Ri_*` on any of the categories `Dᵇc(-, Λ)` that are stable
under `j^*`, `Rj_*` and the fibres of the open unit, without an ambient exceptional adjoint.

## Main statements

- `CategoryTheory.Pretriangulated.rightAdjointObjIsDefined_of_distTriang`: an object `K` sitting
  in a distinguished triangle `F ⟶ K ⟶ R ⟶` with `F` in the essential image of a fully faithful
  `i` and `R` right orthogonal to the shifts of that image has a right adjoint value.
- `CategoryTheory.Pretriangulated.Recollement.isLeftAdjoint`: `i` is a left adjoint.
- `CategoryTheory.Pretriangulated.Recollement.existsUnique_distTriang_counit_unit`: the supported
  localization triangle, with its unique third map.
- `CategoryTheory.Pretriangulated.Recollement.exists_iso_triangle`: any distinguished triangle
  `A ⟶ K ⟶ B ⟶` with `A` in the essential image of `i` and `B` in that of `j_*` is isomorphic to
  the supported localization triangle of `K`, by an isomorphism which is the identity on `K`.
  This is how the supported localization triangle is compared along functors, e.g. for the
  equivariance of the triangle of Weil complexes (blueprint
  `lemma-local-cohomology-right-adjoint--2`).
- `CategoryTheory.Adjunction.isIso_mateEquiv_app`: a criterion for the mate of an isomorphism
  `ΦZ ⋙ i' ≅ i ⋙ Φ` along adjunctions `i ⊣ G`, `i' ⊣ G'` to be invertible, used to compare the
  right adjoints `i^!` along such functors.
-/

@[expose] public section

namespace CategoryTheory

open Limits Category

section Mate

variable {C Z C' Z' : Type*} [Category* C] [Category* Z] [Category* C'] [Category* Z']
  {i : Z ⥤ C} {G : C ⥤ Z} {i' : Z' ⥤ C'} {G' : C' ⥤ Z'} {Φ : C ⥤ C'} {ΦZ : Z ⥤ Z'}

/-- Let `i ⊣ G` and `i' ⊣ G'` be adjunctions with `i'` fully faithful, and `α : ΦZ ⋙ i' ⟶ i ⋙ Φ`
a natural isomorphism. The mate `G ⋙ ΦZ ⟶ Φ ⋙ G'` of `α` is an isomorphism at `K` as soon as
`Φ (i G K)` is isomorphic to `i' G' (Φ K)` compatibly with the counits: `i'` of the mate is
then the composite of `α` and this isomorphism. -/
lemma Adjunction.isIso_mateEquiv_app (adj : i ⊣ G) (adj' : i' ⊣ G') (hi' : i'.FullyFaithful)
    (α : ΦZ ⋙ i' ⟶ i ⋙ Φ) [IsIso α] (K : C)
    (f : Φ.obj (i.obj (G.obj K)) ≅ i'.obj (G'.obj (Φ.obj K)))
    (hf : f.hom ≫ adj'.counit.app (Φ.obj K) = Φ.map (adj.counit.app K)) :
    IsIso ((mateEquiv adj adj' α).app K) := by
  have h : i'.map ((mateEquiv adj adj' α).app K) = α.app (G.obj K) ≫ f.hom := by
    rw [← hi'.map_preimage (α.app (G.obj K) ≫ f.hom)]
    congr 1
    apply (adj'.homEquiv _ _).symm.injective
    simp only [Adjunction.homEquiv_counit, hi'.map_preimage, Category.assoc, hf]
    exact mateEquiv_counit adj adj' α K
  have : IsIso (i'.map ((mateEquiv adj adj' α).app K)) := by
    rw [h]
    infer_instance
  exact hi'.isIso_of_isIso_map _

end Mate

namespace Pretriangulated

variable {C : Type*} [Category* C] [Preadditive C] [HasZeroObject C] [HasShift C ℤ]
  [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]

/-- Let `T` be a distinguished triangle and `M` an object with `Hom(M, T.obj₃) = 0` and
`Hom(M⟦1⟧, T.obj₃) = 0`. Then composition with `T.mor₁` is a bijection
`Hom(M, T.obj₁) ≃ Hom(M, T.obj₂)`. -/
lemma bijective_comp_mor₁_of_subsingleton {T : Triangle C} (hT : T ∈ distTriang C) (M : C)
    [Subsingleton (M ⟶ T.obj₃)] [Subsingleton (M⟦(1 : ℤ)⟧ ⟶ T.obj₃)] :
    Function.Bijective (fun x : M ⟶ T.obj₁ ↦ x ≫ T.mor₁) :=
  ⟨fun _ _ hxy ↦ Triangle.cancel_mor₁_of_subsingleton hT hxy,
    fun y ↦ (Triangle.coyoneda_exact₂ T hT y (Subsingleton.elim _ _)).imp fun _ hx ↦ hx.symm⟩

variable {D : Type*} [Category* D]

/-- Let `F` be fully faithful and `T` a distinguished triangle whose third vertex receives no
maps from the shifts of objects in the image of `F`, with an isomorphism `e : F Q ≅ T.obj₁`. Then
`Q` represents `M ↦ Hom(F M, T.obj₂)`, through `g ↦ F g ≫ e ≫ T.mor₁`. -/
noncomputable def representableByOfDistTriang {F : D ⥤ C} (hF : F.FullyFaithful)
    {T : Triangle C} (hT : T ∈ distTriang C)
    (h₃ : ∀ (M : D) (n : ℤ), Subsingleton ((F.obj M)⟦n⟧ ⟶ T.obj₃)) {Q : D}
    (e : F.obj Q ≅ T.obj₁) : (F.op ⋙ yoneda.obj T.obj₂).RepresentableBy Q where
  homEquiv {M} := Equiv.ofBijective (fun g : M ⟶ Q ↦ F.map g ≫ e.hom ≫ T.mor₁) <| by
    have := h₃ M 1
    have : Subsingleton (F.obj M ⟶ T.obj₃) :=
      have := h₃ M 0
      ((shiftFunctorZero C ℤ).app (F.obj M)).homFromEquiv.symm.subsingleton
    have h := bijective_comp_mor₁_of_subsingleton hT (F.obj M)
    have h' : (fun g : M ⟶ Q ↦ F.map g ≫ e.hom ≫ T.mor₁) =
        (fun x : F.obj M ⟶ T.obj₁ ↦ x ≫ T.mor₁) ∘ (fun x ↦ x ≫ e.hom) ∘ F.map := by
      funext g
      simp
    rw [h']
    exact h.comp (Function.Bijective.comp ⟨fun a b hab ↦ by simpa using hab =≫ e.inv,
      fun y ↦ ⟨y ≫ e.inv, by simp⟩⟩ (hF.map_bijective _ _))
  homEquiv_comp f g := by
    simp

/-- Let `F` be fully faithful and `T` a distinguished triangle whose first vertex is in the
essential image of `F` and whose third vertex receives no maps from the shifts of objects in the
image of `F`. Then the right adjoint of `F` is defined at `T.obj₂`. -/
lemma rightAdjointObjIsDefined_of_distTriang {F : D ⥤ C} (hF : F.FullyFaithful)
    {T : Triangle C} (hT : T ∈ distTriang C)
    (h₃ : ∀ (M : D) (n : ℤ), Subsingleton ((F.obj M)⟦n⟧ ⟶ T.obj₃))
    (h₁ : F.essImage T.obj₁) : F.rightAdjointObjIsDefined T.obj₂ := by
  obtain ⟨Q, ⟨e⟩⟩ := h₁
  exact (representableByOfDistTriang hF hT h₃ e).isRepresentable

/-! ### Recollement data -/

namespace Recollement

variable {Z U : Type*} [Category* Z] [Category* U] [Preadditive U] [HasZeroObject U]
  [HasShift U ℤ] [∀ n : ℤ, (shiftFunctor U n).Additive] [Pretriangulated U]
  (i : Z ⥤ C) (jUp : C ⥤ U) [jUp.CommShift ℤ] [jUp.IsTriangulated] {jLow : U ⥤ C}
  (adj : jUp ⊣ jLow)

omit [Preadditive C] [HasZeroObject C] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
  [HasZeroObject U] [Pretriangulated U] [jUp.IsTriangulated] in
include adj in
/-- **No maps from the closed part to the open part.** If `j^* i = 0`, then
`Hom((i M)⟦n⟧, j_* N) = 0`: by `j^* ⊣ j_*` this is `Hom(j^*((i M)⟦n⟧), N)`, and
`j^*((i M)⟦n⟧) ≅ (j^* i M)⟦n⟧ = 0`. -/
lemma subsingleton_hom_shift (h₀ : ∀ M, IsZero (jUp.obj (i.obj M))) (M : Z) (N : U) (n : ℤ) :
    Subsingleton ((i.obj M)⟦n⟧ ⟶ jLow.obj N) := by
  have hz : IsZero (jUp.obj ((i.obj M)⟦n⟧)) :=
    ((shiftFunctor U n).map_isZero (h₀ M)).of_iso ((jUp.commShiftIso n).app _)
  have : Subsingleton (jUp.obj ((i.obj M)⟦n⟧) ⟶ N) := ⟨fun _ _ ↦ hz.eq_of_src _ _⟩
  exact (adj.homEquiv _ _).symm.subsingleton

omit [Preadditive C] [HasShift C ℤ] [Preadditive U] [HasShift U ℤ] [HasZeroObject C]
  [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
  [HasZeroObject U] [∀ n : ℤ, (shiftFunctor U n).Additive] [Pretriangulated U]
  [jUp.CommShift ℤ] [jUp.IsTriangulated] in
/-- If the counit of `j^* ⊣ j_*` is invertible, `j^*` inverts the unit `K ⟶ j_* j^* K`. -/
lemma isIso_map_unit_app [IsIso adj.counit] (K : C) : IsIso (jUp.map (adj.unit.app K)) := by
  have : IsIso (jUp.map (adj.unit.app K) ≫ adj.counit.app (jUp.obj K)) := by
    rw [adj.left_triangle_components K]
    exact IsIso.id _
  exact IsIso.of_isIso_comp_right _ (adj.counit.app _)

variable {i jUp}

include adj in
/-- **The fibre of the open unit is supported on the closed part.** If the counit of
`j^* ⊣ j_*` is invertible and every object killed by `j^*` lies in the essential image of `i`,
then the unit `K ⟶ j_* j^* K` completes to a distinguished triangle whose first vertex lies in the
essential image of `i`. -/
lemma exists_distTriang_unit [IsIso adj.counit]
    (hess : ∀ K, IsZero (jUp.obj K) → i.essImage K) (K : C) :
    ∃ (F : C) (a : F ⟶ K) (δ : jLow.obj (jUp.obj K) ⟶ F⟦(1 : ℤ)⟧),
      Triangle.mk a (adj.unit.app K) δ ∈ distTriang C ∧ i.essImage F := by
  obtain ⟨F, a, δ, hT⟩ := distinguished_cocone_triangle₁ (adj.unit.app K)
  refine ⟨F, a, δ, hT, hess _ ?_⟩
  have := isIso_map_unit_app jUp adj K
  exact (Triangle.isZero₁_iff_isIso₂ _ (jUp.map_distinguished _ hT)).2 this

include adj in
/-- **The closed part of a recollement is a left adjoint.** In a recollement situation (`i`
fully faithful, `j^* i = 0`, the counit of `j^* ⊣ j_*` invertible, and every object killed by
`j^*` in the essential image of `i`), `i` has a right adjoint `i^!`. -/
lemma isLeftAdjoint (hi : i.FullyFaithful) [IsIso adj.counit]
    (h₀ : ∀ M, IsZero (jUp.obj (i.obj M))) (hess : ∀ K, IsZero (jUp.obj K) → i.essImage K) :
    i.IsLeftAdjoint := by
  refine Functor.isLeftAdjoint_of_rightAdjointObjIsDefined_eq_top ?_
  ext K
  simp only [Pi.top_apply, Prop.top_eq_true, iff_true]
  obtain ⟨F, a, δ, hT, hF⟩ := exists_distTriang_unit adj hess K
  exact rightAdjointObjIsDefined_of_distTriang hi hT
    (fun M n ↦ subsingleton_hom_shift i jUp adj h₀ M _ n) hF

variable {G : C ⥤ Z} (adj' : i ⊣ G)

/-- The *supported localization triangle* of `K`: the counit `i i^! K ⟶ K` of `i ⊣ i^!`, the
unit `K ⟶ j_* j^* K` of `j^* ⊣ j_*`, and a third map `w`. -/
abbrev triangle (K : C) (w : jLow.obj (jUp.obj K) ⟶ (i.obj (G.obj K))⟦(1 : ℤ)⟧) :
    Triangle C where
  obj₁ := i.obj (G.obj K)
  obj₂ := K
  obj₃ := jLow.obj (jUp.obj K)
  mor₁ := adj'.counit.app K
  mor₂ := adj.unit.app K
  mor₃ := w

include adj' in
/-- **Existence of the supported localization triangle.** -/
lemma exists_distTriang_counit_unit (hi : i.FullyFaithful) [IsIso adj.counit]
    (h₀ : ∀ M, IsZero (jUp.obj (i.obj M))) (hess : ∀ K, IsZero (jUp.obj K) → i.essImage K)
    (K : C) : ∃ w, triangle adj adj' K w ∈ distTriang C := by
  obtain ⟨F, a, δ, hT, hF⟩ := exists_distTriang_unit adj hess K
  exact exists_distTriang_counit_of_subsingleton adj' hi hT
    (fun M n ↦ subsingleton_hom_shift i jUp adj h₀ M _ n) hF

include adj' in
/-- **The supported localization triangle**: for every `K` there is a unique map
`w : j_* j^* K ⟶ (i i^! K)⟦1⟧` making `i i^! K ⟶ K ⟶ j_* j^* K ⟶ (i i^! K)⟦1⟧` distinguished. -/
theorem existsUnique_distTriang_counit_unit (hi : i.FullyFaithful) [IsIso adj.counit]
    (h₀ : ∀ M, IsZero (jUp.obj (i.obj M))) (hess : ∀ K, IsZero (jUp.obj K) → i.essImage K)
    (K : C) : ∃! w, triangle adj adj' K w ∈ distTriang C := by
  obtain ⟨w, hw⟩ := exists_distTriang_counit_unit adj adj' hi h₀ hess K
  refine ⟨w, hw, fun w' hw' ↦ ?_⟩
  have : Subsingleton ((triangle adj adj' K w').obj₁⟦(1 : ℤ)⟧ ⟶ (triangle adj adj' K w).obj₃) :=
    subsingleton_hom_shift i jUp adj h₀ _ _ 1
  obtain ⟨τ, hτ⟩ := exists_triangleHom_of_comp_eq_zero hw' hw (𝟙 K) (by
    change adj'.counit.app K ≫ 𝟙 K ≫ adj.unit.app K = 0
    erw [Category.id_comp]
    exact comp_distTriang_mor_zero₁₂ _ hw')
  have h₁ : τ.hom₁ = 𝟙 _ := Triangle.cancel_mor₁_of_subsingleton hw (by
    rw [← τ.comm₁, hτ]
    change adj'.counit.app K ≫ 𝟙 K = 𝟙 _ ≫ adj'.counit.app K
    simp)
  have h₃ : τ.hom₃ = 𝟙 _ := Triangle.cancel_mor₂_of_subsingleton hw' (by
    rw [τ.comm₂, hτ]
    change 𝟙 K ≫ adj.unit.app K = adj.unit.app K ≫ 𝟙 _
    simp)
  have h := τ.comm₃
  rw [h₁, h₃] at h
  simpa using h

omit [HasZeroObject U] [Pretriangulated U] [jUp.IsTriangulated] in
include adj' in
/-- **Naturality of the supported localization triangle.** For `φ : K ⟶ K'` and distinguished
supported localization triangles of `K` and `K'`, the triple `(i i^! φ, φ, j_* j^* φ)` is a
morphism of triangles. -/
lemma exists_triangleHom (h₀ : ∀ M, IsZero (jUp.obj (i.obj M))) {K K' : C} (φ : K ⟶ K')
    {w w'} (hw : triangle adj adj' K w ∈ distTriang C)
    (hw' : triangle adj adj' K' w' ∈ distTriang C) :
    ∃ τ : triangle adj adj' K w ⟶ triangle adj adj' K' w',
      τ.hom₁ = i.map (G.map φ) ∧ τ.hom₂ = φ ∧ τ.hom₃ = jLow.map (jUp.map φ) := by
  have : Subsingleton ((triangle adj adj' K w).obj₁⟦(1 : ℤ)⟧ ⟶ (triangle adj adj' K' w').obj₃) :=
    subsingleton_hom_shift i jUp adj h₀ _ _ 1
  obtain ⟨τ, hτ⟩ := exists_triangleHom_of_comp_eq_zero hw hw' φ (by
    dsimp
    rw [← adj'.counit_naturality_assoc, comp_distTriang_mor_zero₁₂ _ hw', comp_zero])
  refine ⟨τ, Triangle.cancel_mor₁_of_subsingleton hw' ?_, hτ,
    Triangle.cancel_mor₂_of_subsingleton hw ?_⟩
  · rw [← τ.comm₁, hτ]
    exact (adj'.counit_naturality φ).symm
  · rw [τ.comm₂, hτ]
    exact (adj.unit_naturality φ).symm

omit [HasZeroObject U] [Pretriangulated U] [jUp.IsTriangulated] in
include adj' in
/-- **A morphism of supported localization triangles is determined by its middle component.** -/
lemma triangleHom_ext (h₀ : ∀ M, IsZero (jUp.obj (i.obj M))) {K K' : C} {w w'}
    (hw : triangle adj adj' K w ∈ distTriang C) (hw' : triangle adj adj' K' w' ∈ distTriang C)
    {τ τ' : triangle adj adj' K w ⟶ triangle adj adj' K' w'} (h : τ.hom₂ = τ'.hom₂) :
    τ = τ' :=
  have : Subsingleton ((triangle adj adj' K w).obj₁⟦(1 : ℤ)⟧ ⟶ (triangle adj adj' K' w').obj₃) :=
    subsingleton_hom_shift i jUp adj h₀ _ _ 1
  triangleHom_ext_of_subsingleton hw hw' h

omit [Preadditive C] [HasZeroObject C] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
  [HasZeroObject U] [Pretriangulated U] [jUp.IsTriangulated] in
include adj in
/-- `Hom(A⟦n⟧, B) = 0` for `A` in the essential image of `i` and `B` in that of `j_*`. -/
lemma subsingleton_hom_shift_of_essImage (h₀ : ∀ M, IsZero (jUp.obj (i.obj M))) {A B : C}
    (hA : i.essImage A) (hB : jLow.essImage B) (n : ℤ) : Subsingleton (A⟦n⟧ ⟶ B) := by
  obtain ⟨M, ⟨eM⟩⟩ := hA
  obtain ⟨N, ⟨eN⟩⟩ := hB
  have := subsingleton_hom_shift i jUp adj h₀ M N n
  exact (((shiftFunctor C n).mapIso eM).homCongr eN).symm.subsingleton

omit [Preadditive C] [HasZeroObject C] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
  [HasZeroObject U] [Pretriangulated U] [jUp.IsTriangulated] in
include adj in
/-- `Hom(A, B) = 0` for `A` in the essential image of `i` and `B` in that of `j_*`. -/
lemma subsingleton_hom_of_essImage (h₀ : ∀ M, IsZero (jUp.obj (i.obj M))) {A B : C}
    (hA : i.essImage A) (hB : jLow.essImage B) : Subsingleton (A ⟶ B) :=
  have := subsingleton_hom_shift_of_essImage adj h₀ hA hB 0
  ((shiftFunctorZero C ℤ).app A).homFromEquiv.symm.subsingleton

omit [HasZeroObject U] [Pretriangulated U] [jUp.IsTriangulated] in
include adj' in
/-- **The supported localization triangle is determined by its vertices.** A distinguished
triangle `A ⟶ K ⟶ B ⟶ A⟦1⟧` with `A` in the essential image of `i` and `B` in that of `j_*` is
isomorphic to the supported localization triangle `i i^! K ⟶ K ⟶ j_* j^* K ⟶`, by an
isomorphism of triangles which is the identity on `K`. -/
lemma exists_iso_triangle (h₀ : ∀ M, IsZero (jUp.obj (i.obj M))) {T : Triangle C}
    (hT : T ∈ distTriang C) (h₁ : i.essImage T.obj₁) (h₃ : jLow.essImage T.obj₃) {w}
    (hw : triangle adj adj' T.obj₂ w ∈ distTriang C) :
    ∃ e : T ≅ triangle adj adj' T.obj₂ w, e.hom.hom₂ = 𝟙 _ := by
  have hi (M : Z) : i.essImage (i.obj M) := i.obj_mem_essImage M
  have hj (N : U) : jLow.essImage (jLow.obj N) := jLow.obj_mem_essImage N
  obtain ⟨τ, hτ⟩ := exists_triangleHom_of_comp_eq_zero hT hw (𝟙 T.obj₂) (by
    have := subsingleton_hom_of_essImage adj h₀ h₁ (hj (jUp.obj T.obj₂))
    exact Subsingleton.elim _ _)
  obtain ⟨τ', hτ'⟩ := exists_triangleHom_of_comp_eq_zero hw hT (𝟙 T.obj₂) (by
    have := subsingleton_hom_of_essImage adj h₀ (hi (G.obj T.obj₂)) h₃
    exact Subsingleton.elim _ _)
  have := subsingleton_hom_shift_of_essImage adj h₀ h₁ h₃ 1
  have := subsingleton_hom_shift_of_essImage adj h₀ (hi (G.obj T.obj₂)) (hj (jUp.obj T.obj₂)) 1
  refine ⟨{ hom := τ, inv := τ', hom_inv_id := ?_, inv_hom_id := ?_ }, hτ⟩
  · exact triangleHom_ext_of_subsingleton hT hT (by simp [hτ, hτ'])
  · exact triangleHom_ext_of_subsingleton hw hw (by simp [hτ, hτ'])

omit [Preadditive C] [HasZeroObject C] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
  [HasZeroObject U] [Pretriangulated U] [jUp.IsTriangulated] in
include adj adj' in
/-- **`i^! j_* = 0`**: `Hom(M, i^! j_* N) = Hom(i M, j_* N) = 0` for every `M`. -/
lemma isZero_obj_obj [Preadditive Z] (h₀ : ∀ M, IsZero (jUp.obj (i.obj M))) (N : U) :
    IsZero (G.obj (jLow.obj N)) := by
  rw [IsZero.iff_id_eq_zero]
  have : Subsingleton (i.obj (G.obj (jLow.obj N)) ⟶ jLow.obj N) :=
    have := subsingleton_hom_shift i jUp adj h₀ (G.obj (jLow.obj N)) N 0
    ((shiftFunctorZero C ℤ).app _).homFromEquiv.symm.subsingleton
  exact (adj'.homEquiv _ _).symm.injective (Subsingleton.elim _ _)

end Recollement

end Pretriangulated

end CategoryTheory
