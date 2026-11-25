/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.CoproductsOfFiniteAmplitude
public import WeilConjectures.CategoryTheory.DerivedCategory.LeftComplete
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.HomologyProperty
public import WeilConjectures.Mathlib.CategoryTheory.Triangulated.CoproductTriangle

/-!
# Commutation with coproducts from the heart

Let `G : D(C) ⥤ D(D)` be a triangulated functor and `P` a weak Serre class of objects of `C`
closed under coproducts. The complexes with cohomology in `P`
(`DerivedCategory.homologyProperty P`) form a triangulated subcategory stable under the
truncations and coproducts. This file reduces the commutation of `G` with coproducts of such
complexes to statements about objects of `P` placed in degree `0`:

* `DerivedCategory.isLE_obj_of_isLE_of_homologyProperty`: if `G` sends each object of `P` in
  degree `0` into degrees `≤ d`, it sends each bounded complex with cohomology in `P` in degrees
  `≤ n` into degrees `≤ n + d` (dévissage along the truncation triangles);
* `DerivedCategory.isIso_sigmaComparison_of_isGE_of_isLE_of_homologyProperty`: if `G` commutes
  with coproducts of families of objects of `P` in degree `0`, it commutes with coproducts of
  uniformly bounded families of complexes with cohomology in `P` (dévissage, the coproduct of
  the truncation triangles being distinguished, `Pretriangulated.coproductTriangle_distinguished`);
* `DerivedCategory.isIso_sigmaComparison_of_homologyProperty`: if moreover `C` and `D` have exact
  countable products and `G` preserves them and does not lower degrees, then `G` commutes with
  coproducts of arbitrary families of complexes with cohomology in `P`. The amplitude bound
  extends to complexes unbounded below by left completeness
  (`DerivedCategory.isLE_obj_of_forall_isLE_obj_truncGE`), and one concludes with
  `DerivedCategory.isIso_sigmaComparison_of_bounded`.

This is the formal part of blueprint `proposition-compactness-proper-direct-image--2` (2): the
commutation of the proper direct image with direct sums on `Dic(X, Λ)`, from its behaviour on the
ind-constructible sheaves.
-/

@[expose] public section

open CategoryTheory Category Limits Pretriangulated

namespace DerivedCategory

open TStructure (t)

variable {C : Type*} [Category* C] [Abelian C] [HasDerivedCategory C]
  {D : Type*} [Category* D] [Abelian D] [HasDerivedCategory D]

section Amplitude

variable (Φ : DerivedCategory C ⥤ DerivedCategory D) [Φ.CommShift ℤ] [Φ.IsTriangulated] (d : ℤ)
  (P : ObjectProperty C) [P.IsClosedUnderIsomorphisms] [P.ContainsZero]

omit [Φ.IsTriangulated] [P.ContainsZero] in
/-- If a triangulated functor sends every object of `P` placed in degree `0` into degrees `≤ d`,
it sends every complex concentrated in degree `n` with cohomology in `P` into degrees
`≤ n + d`. -/
lemma isLE_obj_of_isGE_of_isLE_of_homologyProperty
    (hΦ : ∀ F : C, P F → (Φ.obj ((singleFunctor C 0).obj F)).IsLE d)
    (M : DerivedCategory C) (hMP : homologyProperty P M) (n : ℤ) [M.IsGE n] [M.IsLE n] :
    (Φ.obj M).IsLE (n + d) := by
  obtain ⟨Y, ⟨e⟩⟩ := exists_iso_singleFunctor_obj_of_isGE_of_isLE M n
  have := hΦ Y (P.prop_of_iso ((homologyFunctor C n).mapIso e ≪≫
    (singleFunctorCompHomologyFunctorIso C n).app Y) (hMP n))
  have : t.IsLE ((Φ.obj ((singleFunctor C 0).obj Y))⟦-n⟧) (n + d) :=
    t.isLE_shift _ d (-n) (n + d) (by lia)
  let e' : (Φ.obj ((singleFunctor C 0).obj Y))⟦-n⟧ ≅ Φ.obj M :=
    (Φ.commShiftIso (-n)).symm.app _ ≪≫
      Φ.mapIso (((singleFunctors C).shiftIso (-n) n 0 (by lia)).app Y) ≪≫ Φ.mapIso e.symm
  exact t.isLE_of_iso e' (n + d)

/-- **Amplitude by dévissage, relative to a class `P`.** If a triangulated functor
`Φ : D(C) ⥤ D(D)` sends every object of `P` placed in degree `0` into degrees `≤ d`, it sends
every bounded complex with cohomology in `P` concentrated in degrees `≤ n` into degrees
`≤ n + d`: by induction on the length, using the truncation triangle
`τ_{< n} M ⟶ M ⟶ τ_{≥ n} M ⟶`. -/
lemma isLE_obj_of_isLE_of_homologyProperty
    (hΦ : ∀ F : C, P F → (Φ.obj ((singleFunctor C 0).obj F)).IsLE d)
    (M : DerivedCategory C) (hM : t.bounded M) (hMP : homologyProperty P M) (n : ℤ) [M.IsLE n] :
    (Φ.obj M).IsLE (n + d) := by
  obtain ⟨⟨a, ha⟩, -⟩ := hM
  suffices h : ∀ (k : ℕ) (M : DerivedCategory C) (n : ℤ), homologyProperty P M →
      M.IsGE (n - k) → M.IsLE n → (Φ.obj M).IsLE (n + d) by
    exact h (n - a).toNat M n hMP (t.isGE_of_ge M _ a (by lia)) inferInstance
  intro k
  induction k with
  | zero =>
    intro M n hMP h₁ h₂
    have : M.IsGE n := by simpa using h₁
    exact isLE_obj_of_isGE_of_isLE_of_homologyProperty Φ d P hΦ M hMP n
  | succ k ih =>
    intro M n hMP h₁ h₂
    have hT := Φ.map_distinguished _ (t.triangleLTGE_distinguished n M)
    refine t.isLE₂ _ hT (n + d) ?_ ?_
    · have : ((t.triangleLTGE n).obj M).obj₁.IsLE (n - 1) :=
        t.isLE_truncLT_obj _ _ _ (by lia)
      have : ((t.triangleLTGE n).obj M).obj₁.IsGE (n - 1 - k) := by
        have : M.IsGE (n - 1 - k) := t.isGE_of_ge M _ (n - ↑(k + 1)) (by lia)
        exact inferInstanceAs (t.IsGE ((t.truncLT n).obj M) _)
      have hP₁ : homologyProperty P ((t.triangleLTGE n).obj M).obj₁ :=
        (homologyProperty P).prop_of_iso ((t.truncLEIsoTruncLT (n - 1) n (by lia)).app M)
          (homologyProperty_truncLE hMP (n - 1))
      have := ih _ (n - 1) hP₁ this inferInstance
      exact t.isLE_of_le (Φ.obj ((t.triangleLTGE n).obj M).obj₁) (n - 1 + d) (n + d) (by lia)
    · have : ((t.triangleLTGE n).obj M).obj₃.IsLE n :=
        inferInstanceAs (t.IsLE ((t.truncGE n).obj M) n)
      have : ((t.triangleLTGE n).obj M).obj₃.IsGE n :=
        inferInstanceAs (t.IsGE ((t.truncGE n).obj M) n)
      exact isLE_obj_of_isGE_of_isLE_of_homologyProperty Φ d P hΦ _
        (homologyProperty_truncGE hMP n) n

end Amplitude

section Coproducts

variable [Abelian.HasKInjectiveResolutions C] [Abelian.HasKInjectiveResolutions D]
  {J : Type*} [HasColimitsOfShape (Discrete J) C] [HasExactColimitsOfShape (Discrete J) C]
  [HasColimitsOfShape (Discrete J) D] [HasExactColimitsOfShape (Discrete J) D]
  (G : DerivedCategory C ⥤ DerivedCategory D)

omit [HasExactColimitsOfShape (Discrete J) C] [HasExactColimitsOfShape (Discrete J) D] in
/-- The comparison map `∐ G(Xⱼ) ⟶ G(∐ Xⱼ)` is an isomorphism for a family isomorphic to one for
which it is. -/
lemma isIso_sigmaComparison_of_iso {X Y : J → DerivedCategory C} (e : ∀ j, X j ≅ Y j)
    (h : IsIso (sigmaComparison G X)) : IsIso (sigmaComparison G Y) := by
  have hnat := sigmaComparison_naturality G fun j ↦ (e j).hom
  have : sigmaComparison G Y = inv (Limits.Sigma.map fun j ↦ G.map (e j).hom) ≫
      sigmaComparison G X ≫ G.map (Limits.Sigma.map fun j ↦ (e j).hom) := by
    rw [hnat, IsIso.inv_hom_id_assoc]
  rw [this]
  infer_instance

omit [HasExactColimitsOfShape (Discrete J) C] [HasExactColimitsOfShape (Discrete J) D] in
/-- If a functor commuting with shifts commutes with the coproduct of a family, it commutes with
the coproduct of the shifted family. -/
lemma isIso_sigmaComparison_shift [G.CommShift ℤ] (X : J → DerivedCategory C) (n : ℤ)
    (h : IsIso (sigmaComparison G X)) : IsIso (sigmaComparison G fun j ↦ (X j)⟦n⟧) := by
  have : PreservesColimit (Discrete.functor X) G := PreservesCoproduct.of_iso_comparison G X
  have : PreservesColimit (Discrete.functor X) (shiftFunctor _ n ⋙ G) :=
    preservesColimit_of_natIso _ (G.commShiftIso n).symm
  have hc := coproductIsCoproduct X
  have : PreservesColimit (Discrete.functor X ⋙ shiftFunctor _ n) G :=
    preservesColimit_of_preserves_colimit_cocone (isColimitOfPreserves (shiftFunctor _ n) hc)
      (isColimitOfPreserves (shiftFunctor _ n ⋙ G) hc)
  have : PreservesColimit (Discrete.functor fun j ↦ (X j)⟦n⟧) G :=
    preservesColimit_of_iso_diagram G
      (Discrete.natIsoFunctor (F := Discrete.functor X ⋙ shiftFunctor _ n))
  infer_instance

omit [HasExactColimitsOfShape (Discrete J) C] [HasExactColimitsOfShape (Discrete J) D] in
/-- **Two out of three for the commutation with coproducts.** For a family of distinguished
triangles `Aⱼ ⟶ Bⱼ ⟶ Cⱼ ⟶ Aⱼ⟦1⟧`, if a triangulated functor `G` commutes with the coproducts of
the `Aⱼ` and of the `Cⱼ`, it commutes with the coproduct of the `Bⱼ`: the comparison maps form
a morphism from the coproduct of the image triangles to the image of the coproduct triangle,
both distinguished. -/
lemma isIso_sigmaComparison_obj₂ [G.CommShift ℤ] [G.IsTriangulated]
    (T : J → Triangle (DerivedCategory C)) (hT : ∀ j, T j ∈ distTriang _)
    (h₁ : IsIso (sigmaComparison G fun j ↦ (T j).obj₁))
    (h₃ : IsIso (sigmaComparison G fun j ↦ (T j).obj₃)) :
    IsIso (sigmaComparison G fun j ↦ (T j).obj₂) := by
  have h₃' (j : J) : Sigma.ι (fun j ↦ G.obj (T j).obj₃) j ≫
      ((Limits.Sigma.map fun j ↦ G.map (T j).mor₃ ≫
          (G.commShiftIso (1 : ℤ)).hom.app (T j).obj₁) ≫
        sigmaComparison (shiftFunctor _ (1 : ℤ)) fun j ↦ G.obj (T j).obj₁) ≫
        (sigmaComparison G fun j ↦ (T j).obj₁)⟦(1 : ℤ)⟧' =
      Sigma.ι (fun j ↦ G.obj (T j).obj₃) j ≫ sigmaComparison G (fun j ↦ (T j).obj₃) ≫
        G.map ((Limits.Sigma.map fun j ↦ (T j).mor₃) ≫
          sigmaComparison (shiftFunctor _ (1 : ℤ)) fun j ↦ (T j).obj₁) ≫
        (G.commShiftIso (1 : ℤ)).hom.app (∐ fun j ↦ (T j).obj₁) := by
    simp only [assoc, Functor.comp_obj, Limits.Sigma.ι_map_assoc, ι_comp_sigmaComparison_assoc]
    rw [← Functor.map_comp (shiftFunctor _ (1 : ℤ)), ι_comp_sigmaComparison,
      ← G.map_comp_assoc, Limits.Sigma.ι_map_assoc,
      ι_comp_sigmaComparison, G.map_comp_assoc, Functor.commShiftIso_hom_naturality]
  let φ : coproductTriangle (fun j ↦ G.mapTriangle.obj (T j)) ⟶
      G.mapTriangle.obj (coproductTriangle T) :=
    Triangle.homMk _ _ (sigmaComparison G fun j ↦ (T j).obj₁)
      (sigmaComparison G fun j ↦ (T j).obj₂) (sigmaComparison G fun j ↦ (T j).obj₃)
      (sigmaComparison_naturality G fun j ↦ (T j).mor₁).symm
      (sigmaComparison_naturality G fun j ↦ (T j).mor₂).symm
      (Sigma.hom_ext _ _ h₃')
  exact isIso₂_of_isIso₁₃ φ
    (coproductTriangle_distinguished _ fun j ↦ G.map_distinguished _ (hT j))
    (G.map_distinguished _ (coproductTriangle_distinguished T hT)) h₁ h₃

variable (P : ObjectProperty C) [P.IsClosedUnderIsomorphisms] [P.ContainsZero]

omit [HasExactColimitsOfShape (Discrete J) C] [HasExactColimitsOfShape (Discrete J) D] in
/-- **Commutation with coproducts of uniformly bounded families, by dévissage.** If a triangulated
functor `G` commutes with coproducts of families of objects of `P` placed in degree `0`, it
commutes with coproducts of families of complexes with cohomology in `P` concentrated in a
common interval `[a, b]`. -/
theorem isIso_sigmaComparison_of_isGE_of_isLE_of_homologyProperty [G.CommShift ℤ]
    [G.IsTriangulated]
    (hG : ∀ N : J → C, (∀ j, P (N j)) →
      IsIso (sigmaComparison G fun j ↦ (singleFunctor C 0).obj (N j)))
    (N : J → DerivedCategory C) (a b : ℤ)
    (hN : ∀ j, homologyProperty P (N j) ∧ (N j).IsGE a ∧ (N j).IsLE b) :
    IsIso (sigmaComparison G N) := by
  -- families concentrated in a single degree
  have hbase (N : J → DerivedCategory C) (n : ℤ)
      (hN : ∀ j, homologyProperty P (N j) ∧ (N j).IsGE n ∧ (N j).IsLE n) :
      IsIso (sigmaComparison G N) := by
    have hY (j : J) := @exists_iso_singleFunctor_obj_of_isGE_of_isLE C _ _ _ (N j) n
      (hN j).2.1 (hN j).2.2
    choose Y hY using hY
    let e (j : J) : ((singleFunctor C 0).obj (Y j))⟦-n⟧ ≅ N j :=
      ((singleFunctors C).shiftIso (-n) n 0 (by lia)).app (Y j) ≪≫ (hY j).some.symm
    refine isIso_sigmaComparison_of_iso G e (isIso_sigmaComparison_shift G _ (-n)
      (hG Y fun j ↦ ?_))
    exact P.prop_of_iso ((homologyFunctor C n).mapIso (hY j).some ≪≫
      (singleFunctorCompHomologyFunctorIso C n).app (Y j)) ((hN j).1 n)
  suffices h : ∀ (k : ℕ) (N : J → DerivedCategory C) (n : ℤ),
      (∀ j, homologyProperty P (N j) ∧ (N j).IsGE (n - k) ∧ (N j).IsLE n) →
        IsIso (sigmaComparison G N) by
    refine h (b - a).toNat N b fun j ↦ ⟨(hN j).1, ?_, (hN j).2.2⟩
    have := (hN j).2.1
    exact t.isGE_of_ge (N j) _ a (by lia)
  intro k
  induction k with
  | zero =>
    intro N n hN
    exact hbase N n fun j ↦ ⟨(hN j).1, by simpa using (hN j).2.1, (hN j).2.2⟩
  | succ k ih =>
    intro N n hN
    refine isIso_sigmaComparison_obj₂ G (fun j ↦ (t.triangleLTGE n).obj (N j))
      (fun j ↦ t.triangleLTGE_distinguished n (N j)) (ih _ (n - 1) fun j ↦ ?_)
      (hbase _ n fun j ↦ ?_)
    · have := (hN j).2.1
      have : (N j).IsGE (n - 1 - k) := t.isGE_of_ge (N j) _ (n - ↑(k + 1)) (by lia)
      refine ⟨(homologyProperty P).prop_of_iso
        ((t.truncLEIsoTruncLT (n - 1) n (by lia)).app (N j))
          (homologyProperty_truncLE (hN j).1 (n - 1)), ?_, ?_⟩
      · exact inferInstanceAs (t.IsGE ((t.truncLT n).obj (N j)) _)
      · exact t.isLE_truncLT_obj _ _ _ (by lia)
    · have := (hN j).2.2
      exact ⟨homologyProperty_truncGE (hN j).1 n,
        inferInstanceAs (t.IsGE ((t.truncGE n).obj (N j)) n),
        inferInstanceAs (t.IsLE ((t.truncGE n).obj (N j)) n)⟩

variable [P.IsClosedUnderKernels] [P.IsClosedUnderCokernels] [P.IsClosedUnderExtensions]
  [P.IsClosedUnderColimitsOfShape (Discrete J)]
  [HasLimitsOfShape (Discrete ℕ) C] [HasExactLimitsOfShape (Discrete ℕ) C]
  [HasLimitsOfShape (Discrete ℕ) D] [HasExactLimitsOfShape (Discrete ℕ) D]

omit [P.IsClosedUnderIsomorphisms] [P.ContainsZero] [P.IsClosedUnderKernels]
  [P.IsClosedUnderCokernels] [P.IsClosedUnderExtensions] [HasLimitsOfShape (Discrete ℕ) C]
  [HasExactLimitsOfShape (Discrete ℕ) C] [HasLimitsOfShape (Discrete ℕ) D]
  [HasExactLimitsOfShape (Discrete ℕ) D] in
/-- Complexes with cohomology in a class closed under coproducts are closed under coproducts. -/
lemma homologyProperty_sigma (N : J → DerivedCategory C) (hN : ∀ j, homologyProperty P (N j)) :
    homologyProperty P (∐ N) := fun n ↦
  P.prop_of_isColimit
    (isColimitOfPreserves (homologyFunctor C n) (coproductIsCoproduct N)) fun j ↦ hN j.as n

/-- **Commutation with coproducts from the heart.** Let `P` be a weak Serre class of objects of
`C` closed under coproducts, where `C` and `D` have exact coproducts and exact countable
products, and let `G : D(C) ⥤ D(D)` be a triangulated functor preserving countable products and
not lowering degrees. If `G` sends the objects of `P` placed in degree `0` into degrees `≤ d`
and commutes with coproducts of families of such objects, then `G` commutes with coproducts of
arbitrary families of complexes with cohomology in `P`. -/
theorem isIso_sigmaComparison_of_homologyProperty [G.CommShift ℤ] [G.IsTriangulated]
    [PreservesLimitsOfShape (Discrete ℕ) G] (d : ℤ)
    (hG₁ : ∀ F : C, P F → (G.obj ((singleFunctor C 0).obj F)).IsLE d)
    (hG₂ : ∀ (X : DerivedCategory C) (a : ℤ), X.IsGE a → (G.obj X).IsGE a)
    (hG₃ : ∀ N : J → C, (∀ j, P (N j)) →
      IsIso (sigmaComparison G fun j ↦ (singleFunctor C 0).obj (N j)))
    (M : J → DerivedCategory C) (hM : ∀ j, homologyProperty P (M j)) :
    IsIso (sigmaComparison G M) := by
  refine isIso_sigmaComparison_of_bounded G (homologyProperty P)
    (fun _ n hX ↦ ⟨homologyProperty_truncLE hX n, homologyProperty_truncGE hX n⟩)
    (homologyProperty_sigma P) (d + 1) (fun X b hX hXb ↦ ?_) hG₂
    (fun N a b hN ↦ isIso_sigmaComparison_of_isGE_of_isLE_of_homologyProperty G P hG₃ N a b hN)
    M hM
  have := isLE_obj_of_forall_isLE_obj_truncGE G X (b + d) fun n ↦
    isLE_obj_of_isLE_of_homologyProperty G d P hG₁ _
      ⟨⟨-(n : ℤ), inferInstance⟩, ⟨b, inferInstance⟩⟩ (homologyProperty_truncGE hX _) b
  rwa [← add_assoc]

end Coproducts

end DerivedCategory
