/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.Algebra.Homology.DerivedCategory.TowerLimit
public import WeilConjectures.Algebra.Homology.DerivedCategory.TowerLimitRange
public import WeilConjectures.Algebra.Homology.HomotopyCategory.Products
public import WeilConjectures.CategoryTheory.Triangulated.HomotopyLimit.Basic
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.TStructure

/-!
# Left completeness of derived categories with exact countable products

Let `C` be an abelian category with K-injective resolutions in which countable products exist
and are exact (for instance sheaves of modules on a replete site, such as the pro-étale site).
Then the derived category `D(C)` is *left complete*: every object `K` is the homotopy limit of
the tower `⋯ ⟶ τ_{≥ -1} K ⟶ τ_{≥ 0} K` of its truncations
(`DerivedCategory.isHomotopyLimit_truncGECone`, Bhatt–Scholze, *The pro-étale topology for
schemes*, Proposition 3.3.3, blueprint `proposition-left-completeness`).

Indeed, let `W` be the homotopy limit, the fibre of `1 - t` on `∏ₙ τ_{≥ -n} K`. Products being
exact, `Hⁱ(∏ₙ τ_{≥ -n} K) = ∏ₙ Hⁱ(τ_{≥ -n} K)`, and the tower `Hⁱ(τ_{≥ -n} K)` vanishes for
`n < -i` and is constant equal to `Hⁱ(K)` from there on. For such a tower `1 - t` is a split
epimorphism (`CategoryTheory.Limits.epi_one_sub_of_isZero_of_isIso`) and its kernel is the
limit `Hⁱ(K)` (`CategoryTheory.Limits.isLimitOfIsZeroOfIsIso`). The homology sequence of the
Milnor triangle then shows that `K ⟶ W` induces isomorphisms on all `Hⁱ`.

As a consequence, a triangulated functor `G` preserving countable products, with values in a
derived category with exact countable products, sends an object `K` into degrees `≤ b + 1` as
soon as it sends all truncations `τ_{≥ -n} K` into degrees `≤ b`
(`DerivedCategory.isLE_obj_of_forall_isLE_obj_truncGE`).
-/

@[expose] public section

open CategoryTheory Category Limits Opposite Pretriangulated

namespace CategoryTheory.Limits

variable {C : Type*} [Category* C] [Preadditive C]

/-- A cone over a tower `F` whose terms vanish below `N` and whose legs are isomorphisms from
`N` on is a limit cone. -/
noncomputable def isLimitOfIsZeroOfIsIso {F : ℕᵒᵖ ⥤ C} (c : Cone F) (N : ℕ)
    (hz : ∀ n < N, IsZero (F.obj (op n))) (hi : ∀ n, N ≤ n → IsIso (c.π.app (op n))) :
    IsLimit c :=
  have := hi N le_rfl
  { lift s := s.π.app (op N) ≫ inv (c.π.app (op N))
    fac s j := by
      obtain ⟨n⟩ := j
      by_cases hn : n < N
      · exact (hz n hn).eq_of_tgt _ _
      · have := hi n (by lia)
        have hs := s.w (homOfLE (show N ≤ n by lia)).op
        have hc := c.w (homOfLE (show N ≤ n by lia)).op
        have : IsIso (c.π.app (op n) ≫ F.map (homOfLE (show N ≤ n by lia)).op) := by
          rw [hc]
          infer_instance
        have := IsIso.of_isIso_comp_left (c.π.app (op n)) (F.map (homOfLE (show N ≤ n by lia)).op)
        have key : inv (c.π.app (op N)) ≫ c.π.app (op n) =
            inv (F.map (homOfLE (show N ≤ n by lia)).op) := by
          rw [IsIso.inv_comp_eq, ← hc, assoc, IsIso.hom_inv_id, comp_id]
        rw [assoc, key, ← hs, assoc, IsIso.hom_inv_id, comp_id]
    uniq s m hm := by
      rw [← hm (op N)]
      simp }

/-- For a tower `F` whose terms vanish below `N`, and a cone `c` over it whose legs are
isomorphisms from `N` on, the map `1 - t` on a product `∏ Fₙ` is a split epimorphism, where `t`
has components `∏ Fₙ ⟶ Fₙ₊₁ ⟶ Fₙ`: a section has components
`y ↦ -(∑_{N ≤ k < n} yₖ) ` (transported along the legs of `c`). -/
lemma epi_one_sub_of_isZero_of_isIso {F : ℕᵒᵖ ⥤ C} {P : Fan fun n : ℕ ↦ F.obj (op n)}
    (hP : IsLimit P) (t : P.pt ⟶ P.pt)
    (ht : ∀ n : ℕ, t ≫ P.proj n = P.proj (n + 1) ≫ F.map (homOfLE n.le_succ).op)
    (c : Cone F) (N : ℕ) (hz : ∀ n < N, IsZero (F.obj (op n)))
    (hi : ∀ n, N ≤ n → IsIso (c.π.app (op n))) : Epi (𝟙 P.pt - t) := by
  classical
  let ρ (n : ℕ) : F.obj (op n) ⟶ c.pt :=
    if h : N ≤ n then (have := hi n h; inv (c.π.app (op n))) else 0
  have hρ (n : ℕ) (h : N ≤ n) : ρ n ≫ c.π.app (op n) = 𝟙 _ := by
    have := hi n h
    simp [ρ, h]
  let σ : P.pt ⟶ P.pt :=
    Fan.IsLimit.lift hP fun n ↦ -(∑ k ∈ Finset.Ico N n, P.proj k ≫ ρ k) ≫ c.π.app (op n)
  have hσ : σ ≫ (𝟙 P.pt - t) = 𝟙 _ := Fan.IsLimit.hom_ext hP _ _ fun n ↦ by
    by_cases hn : n < N
    · exact (hz n hn).eq_of_tgt _ _
    · have hw : c.π.app (op (n + 1)) ≫ F.map (homOfLE n.le_succ).op = c.π.app (op n) :=
        c.w _
      simp only [Preadditive.comp_sub, comp_id, Preadditive.sub_comp, assoc, ht, σ,
        Fan.IsLimit.fac, Fan.IsLimit.fac_assoc, id_comp, hw, Finset.sum_Ico_succ_top
          (show N ≤ n by lia), Preadditive.neg_comp, Preadditive.add_comp, hρ n (by lia)]
      abel
  have : IsSplitEpi (𝟙 P.pt - t) := ⟨⟨⟨σ, hσ⟩⟩⟩
  infer_instance

/-- In a category with kernels, let `f : A ⟶ B` and `g : B ⟶ D` with `g` a monomorphism, such
that `f ≫ g` is a kernel of some `h` with `g ≫ h = 0`. Then `f` is an isomorphism. -/
lemma isIso_of_mono_of_isLimit_kernelFork {A B D E : C} (f : A ⟶ B) (g : B ⟶ D) (h : D ⟶ E)
    [Mono g] (hgh : g ≫ h = 0) (hfgh : (f ≫ g) ≫ h = 0)
    (hk : IsLimit (KernelFork.ofι _ hfgh)) : IsIso f := by
  have : Mono (f ≫ g) := mono_of_isLimit_fork hk
  obtain ⟨u, hu⟩ := KernelFork.IsLimit.lift' hk g hgh
  have hu' : u ≫ f ≫ g = g := by simpa using hu
  refine ⟨⟨u, ?_, ?_⟩⟩
  · rw [← cancel_mono (f ≫ g), assoc, hu', id_comp]
  · rw [← cancel_mono g, assoc, hu', id_comp]

end CategoryTheory.Limits

namespace DerivedCategory

variable {C : Type*} [Category* C] [Abelian C] [HasDerivedCategory C]

open TStructure (t)

/-- The tower `⋯ ⟶ τ_{≥ -1} K ⟶ τ_{≥ 0} K` of truncations of an object `K` of `D(C)`. -/
noncomputable def truncGETower (K : DerivedCategory C) : ℕᵒᵖ ⥤ DerivedCategory C where
  obj n := (t.truncGE (-(n.unop : ℤ))).obj K
  map {m n} f := (t.natTransTruncGEOfLE (-(m.unop : ℤ)) (-(n.unop : ℤ))
    (by have := leOfHom f.unop; lia)).app K
  map_id n := t.natTransTruncGEOfLE_refl_app _ K
  map_comp f g := (t.natTransTruncGEOfLE_trans_app _ _ _ _ _ K).symm

/-- The cone of truncation maps `K ⟶ τ_{≥ -n} K` over the tower of truncations of `K`. -/
@[simps]
noncomputable def truncGECone (K : DerivedCategory C) : Cone (truncGETower K) where
  pt := K
  π :=
    { app n := (t.truncGEπ (-(n.unop : ℤ))).app K
      naturality m n f := by
        dsimp [truncGETower]
        rw [id_comp, t.π_natTransTruncGEOfLE_app] }

lemma truncGETower_obj (K : DerivedCategory C) (n : ℕ) :
    (truncGETower K).obj (op n) = (t.truncGE (-(n : ℤ))).obj K :=
  rfl

instance (K : DerivedCategory C) (n : ℕ) : ((truncGETower K).obj (op n)).IsGE (-(n : ℤ)) :=
  inferInstanceAs (t.IsGE ((t.truncGE (-(n : ℤ))).obj K) _)

variable [Abelian.HasKInjectiveResolutions C] [HasLimitsOfShape (Discrete ℕ) C]
  [HasExactLimitsOfShape (Discrete ℕ) C]

/-- Blueprint `proposition-left-completeness`: in the derived category of an abelian category with
exact countable products, every object `K` is the homotopy limit of the tower of its truncations
`τ_{≥ -n} K` (Bhatt–Scholze, *The pro-étale topology for schemes*, Proposition 3.3.3). -/
theorem isHomotopyLimit_truncGECone (K : DerivedCategory C) :
    IsHomotopyLimit (truncGECone K) := by
  let F := truncGETower K
  let c := truncGECone K
  let P : Fan fun n : ℕ ↦ F.obj (op n) := Fan.mk _ (Pi.π _)
  let hP : IsLimit P := productIsProduct _
  let τ := towerShift hP
  have hτ (n : ℕ) : τ ≫ P.proj n = P.proj (n + 1) ≫ F.map (homOfLE n.le_succ).op :=
    Fan.IsLimit.fac hP _ n
  obtain ⟨W, ι, δ, hT⟩ := distinguished_cocone_triangle₁ (𝟙 P.pt - τ)
  let ℓ : K ⟶ P.pt := Fan.IsLimit.lift hP fun n ↦ c.π.app (op n)
  have hℓ : ℓ ≫ (𝟙 P.pt - τ) = 0 := Fan.IsLimit.lift_π_comp_one_sub_eq_zero hP τ hτ c
  obtain ⟨u, hu⟩ := Triangle.coyoneda_exact₂ _ hT ℓ hℓ
  -- the homology of the product and of `1 - t`
  have hH (j : ℤ) : IsLimit (Fan.mk ((homologyFunctor C j).obj P.pt)
      fun n ↦ (homologyFunctor C j).map (P.proj n)) :=
    isLimitFanMkObjOfIsLimit (homologyFunctor C j) _ _ hP
  have hHτ (j : ℤ) (n : ℕ) : (homologyFunctor C j).map τ ≫
      (Fan.mk ((homologyFunctor C j).obj P.pt)
        fun n ↦ (homologyFunctor C j).map (P.proj n)).proj n =
      (Fan.mk ((homologyFunctor C j).obj P.pt)
        fun n ↦ (homologyFunctor C j).map (P.proj n)).proj (n + 1) ≫
        (F ⋙ homologyFunctor C j).map (homOfLE n.le_succ).op := by
    simp only [fan_mk_proj, Functor.comp_map, ← Functor.map_comp, hτ]
  have hz (j : ℤ) (n : ℕ) (hn : n < (-j).toNat) :
      IsZero ((F ⋙ homologyFunctor C j).obj (op n)) :=
    isZero_of_isGE ((truncGETower K).obj (op n)) (-(n : ℤ)) j (by lia)
  have hi (j : ℤ) (n : ℕ) (hn : (-j).toNat ≤ n) :
      IsIso (((homologyFunctor C j).mapCone c).π.app (op n)) :=
    isIso_homologyFunctor_map_truncGEπ_app K _ _ (by lia)
  have hepi (j : ℤ) : Epi ((homologyFunctor C j).map (𝟙 P.pt - τ)) := by
    rw [Functor.map_sub, CategoryTheory.Functor.map_id]
    exact epi_one_sub_of_isZero_of_isIso (hH j) _ (hHτ j) _ _ (hz j) (hi j)
  have hiso : IsIso u := by
    rw [isIso_iff]
    intro i
    have : Mono ((homologyFunctor C i).map ι) :=
      (HomologySequence.mono_homologyMap_mor₁_iff _ hT (i - 1) i (by lia)).2
        ((HomologySequence.epi_homologyMap_mor₂_iff _ hT (i - 1) i (by lia)).1 (hepi (i - 1)))
    have hk := Fan.IsLimit.isLimitKernelForkOneSub (hH i) _ (hHτ i)
      (isLimitOfIsZeroOfIsIso _ _ (hz i) (hi i))
    have hlift : Fan.IsLimit.lift (hH i)
        (fun n ↦ ((homologyFunctor C i).mapCone c).π.app (op n)) =
        (homologyFunctor C i).map u ≫ (homologyFunctor C i).map ι := by
      refine Fan.IsLimit.hom_ext (hH i) _ _ fun n ↦ ?_
      have hu' : u ≫ ι = ℓ := hu.symm
      rw [Fan.IsLimit.fac]
      simp only [Functor.mapCone_π_app, fan_mk_proj, assoc, ← Functor.map_comp]
      rw [reassoc_of% hu']
      exact congrArg _ (Fan.IsLimit.fac hP (fun n ↦ c.π.app (op n)) n).symm
    have hιτ : (homologyFunctor C i).map ι ≫ (homologyFunctor C i).map (𝟙 P.pt - τ) = 0 := by
      have h0 : ι ≫ (𝟙 P.pt - τ) = 0 := comp_distTriang_mor_zero₁₂ _ hT
      rw [← Functor.map_comp, h0, Functor.map_zero]
    have hfgh : ((homologyFunctor C i).map u ≫ (homologyFunctor C i).map ι) ≫
        (𝟙 _ - (homologyFunctor C i).map τ) = 0 := by
      rw [← CategoryTheory.Functor.map_id, ← Functor.map_sub, assoc, hιτ, comp_zero]
    have hιτ' : (homologyFunctor C i).map ι ≫ (𝟙 _ - (homologyFunctor C i).map τ) = 0 := by
      rwa [Functor.map_sub, CategoryTheory.Functor.map_id] at hιτ
    refine isIso_of_mono_of_isLimit_kernelFork _ _ _ hιτ' hfgh
      (IsLimit.ofIsoLimit hk (Fork.ext (Iso.refl _) ?_))
    exact (id_comp _).trans hlift.symm
  refine ⟨P, hP, δ ≫ (inv u)⟦(1 : ℤ)⟧', isomorphic_distinguished _ hT _
    (Triangle.isoMk _ _ (asIso u) (Iso.refl _) (Iso.refl _) ?_ ?_ ?_)⟩
  · simpa [ℓ, c] using hu
  · simp [τ]
  · simp [τ]

section Amplitude

variable {D : Type*} [Category* D] [Abelian D] [HasDerivedCategory D]
  [Abelian.HasKInjectiveResolutions D] [HasLimitsOfShape (Discrete ℕ) D]
  [HasExactLimitsOfShape (Discrete ℕ) D]

omit [HasDerivedCategory C] [Abelian.HasKInjectiveResolutions C]
  [HasLimitsOfShape (Discrete ℕ) C] [HasExactLimitsOfShape (Discrete ℕ) C] in
/-- In the derived category of an abelian category with exact countable products, the point of
a homotopy limit cone over a tower of objects in degrees `≤ b` lies in degrees `≤ b + 1`. -/
lemma isLE_of_isHomotopyLimit {F : ℕᵒᵖ ⥤ DerivedCategory D} {c : Cone F}
    (hc : IsHomotopyLimit c) (b : ℤ) (hF : ∀ n : ℕ, (F.obj (op n)).IsLE b) :
    c.pt.IsLE (b + 1) := by
  obtain ⟨P, hP, δ, hT⟩ := hc
  have hPb : P.pt.IsLE b := by
    rw [isLE_iff]
    intro i hi
    exact isZero_homologyFunctor_obj_of_isLimit hP i fun n ↦
      isZero_of_isLE _ b i hi (hX := hF n)
  have : (P.pt⟦(-1 : ℤ)⟧).IsLE (b + 1) := t.isLE_shift _ b (-1) (b + 1) (by lia)
  have : P.pt.IsLE (b + 1) := t.isLE_of_le _ b (b + 1) (by lia)
  exact t.isLE₂ _ (inv_rot_of_distTriang _ hT) (b + 1)
    (inferInstanceAs ((P.pt⟦(-1 : ℤ)⟧).IsLE (b + 1))) this

/-- Let `G : D(C) ⥤ D(D)` be a triangulated functor preserving countable products, where `C` and
`D` have exact countable products. If `G` sends every truncation `τ_{≥ -n} K` into degrees
`≤ b`, it sends `K` into degrees `≤ b + 1`: `K` is the homotopy limit of its truncations
(`DerivedCategory.isHomotopyLimit_truncGECone`), and `G` preserves homotopy limits. -/
lemma isLE_obj_of_forall_isLE_obj_truncGE (G : DerivedCategory C ⥤ DerivedCategory D)
    [G.CommShift ℤ] [G.IsTriangulated] [PreservesLimitsOfShape (Discrete ℕ) G]
    (K : DerivedCategory C) (b : ℤ)
    (hK : ∀ n : ℕ, (G.obj ((t.truncGE (-(n : ℤ))).obj K)).IsLE b) :
    (G.obj K).IsLE (b + 1) :=
  isLE_of_isHomotopyLimit ((isHomotopyLimit_truncGECone K).map G) b hK

end Amplitude

end DerivedCategory
