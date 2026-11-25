/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.Algebra.Homology.DerivedCategory.TowerLimitRange

/-!
# The Milnor sequence of a homotopy limit in a derived category

Let `C` be an abelian category with exact countable products and K-injective resolutions, and
let `c` be a homotopy limit cone over a tower `F : ℕᵒᵖ ⥤ D(C)`, i.e. `c.pt = R lim Fₙ` fits into
a distinguished Milnor triangle `c.pt ⟶ ∏ Fₙ ──1 - t──▶ ∏ Fₙ ⟶ c.pt[1]`. Cohomology commutes
with countable products, so the long exact cohomology sequence of this triangle yields, for
`i + 1 = j`, the **Milnor short exact sequence**
```
  0 ⟶ R¹lim Hⁱ(Fₙ) ⟶ Hʲ(R lim Fₙ) ⟶ lim Hʲ(Fₙ) ⟶ 0,
```
where `R¹lim Hⁱ(Fₙ)` is the cokernel of `1 - t` on `∏ Hⁱ(Fₙ)` (Stacks 0CQD, 0940; blueprint
`proposition-milnor-sequence--2`, `proposition-milnor-sequence`).

## Main results

- `DerivedCategory.shortExact_milnor_of_isHomotopyLimit`: the Milnor short exact sequence.
- `DerivedCategory.isIso_lift_homologyFunctor_mapCone_of_isHomotopyLimit`: if `1 - t` is an
  epimorphism on `∏ Hⁱ(Fₙ)` (`R¹lim = 0`, e.g. under Mittag-Leffler), then
  `Hʲ(R lim Fₙ) ≅ lim Hʲ(Fₙ)`.
-/

@[expose] public section

open CategoryTheory Category Limits Opposite Pretriangulated

namespace DerivedCategory

variable {C : Type*} [Category* C] [Abelian C] [HasDerivedCategory C]
  [Abelian.HasKInjectiveResolutions C] [HasLimitsOfShape (Discrete ℕ) C]
  [HasExactLimitsOfShape (Discrete ℕ) C] {F : ℕᵒᵖ ⥤ DerivedCategory C} {c : Cone F}

/-- **The Milnor short exact sequence** (Stacks 0CQD, blueprint `proposition-milnor-sequence--2`).
Let `c` be a homotopy limit cone over a tower `F` in `D(C)`, let `i + 1 = j`, let `P` be a
product of the `Hⁱ(Fₙ)` with its transition endomorphism `t` (components
`∏ Hⁱ(Fₘ) ⟶ Hⁱ(Fₙ₊₁) ⟶ Hⁱ(Fₙ)`) and let `d` be a limit cone over `n ↦ Hʲ(Fₙ)`. Then there is
a short exact sequence
`0 ⟶ coker (1 - t) ⟶ Hʲ(c.pt) ⟶ d.pt ⟶ 0`,
i.e. `0 ⟶ R¹lim Hⁱ(Fₙ) ⟶ Hʲ(R lim Fₙ) ⟶ lim Hʲ(Fₙ) ⟶ 0`, whose second map is induced by the
legs of `c`. -/
theorem shortExact_milnor_of_isHomotopyLimit (hc : IsHomotopyLimit c) (i j : ℤ)
    (hij : i + 1 = j) {P : Fan fun n : ℕ ↦ (homologyFunctor C i).obj (F.obj (op n))}
    (hP : IsLimit P) (t : P.pt ⟶ P.pt)
    (ht : ∀ n : ℕ, t ≫ P.proj n =
      P.proj (n + 1) ≫ (homologyFunctor C i).map (F.map (homOfLE n.le_succ).op))
    {d : Cone (F ⋙ homologyFunctor C j)} (hd : IsLimit d) :
    ∃ (a : cokernel (𝟙 P.pt - t) ⟶ (homologyFunctor C j).obj c.pt)
      (hz : a ≫ hd.lift ((homologyFunctor C j).mapCone c) = 0),
      (ShortComplex.mk _ _ hz).ShortExact := by
  let Hi := homologyFunctor C i
  let Hj := homologyFunctor C j
  let P' : Fan fun n : ℕ ↦ F.obj (op n) := Fan.mk _ (Pi.π _)
  let hP' : IsLimit P' := productIsProduct _
  obtain ⟨δ, hT⟩ := hc.exists_distTriang hP'
  let p := Fan.IsLimit.lift hP' fun n ↦ c.π.app (op n)
  have hp (n : ℕ) : p ≫ P'.proj n = c.π.app (op n) := Fan.IsLimit.fac hP' _ n
  let s := towerShift hP'
  let δH := HomologySequence.δ (Triangle.mk p (𝟙 _ - s) δ) i j hij
  -- degree `i`: identify `Hⁱ(∏ Fₙ)` with `P.pt`
  let hPi : IsLimit (Fan.mk (Hi.obj P'.pt) fun n ↦ Hi.map (P'.proj n)) :=
    isLimitFanMkObjOfIsLimit Hi _ _ hP'
  let e : Hi.obj P'.pt ≅ P.pt := hPi.conePointUniqueUpToIso hP
  have he (n : ℕ) : e.hom ≫ P.proj n = Hi.map (P'.proj n) :=
    hPi.conePointUniqueUpToIso_hom_comp hP ⟨n⟩
  have hcomm : Hi.map (𝟙 _ - s) ≫ e.hom = e.hom ≫ (𝟙 _ - t) := by
    refine Fan.IsLimit.hom_ext hP _ _ fun n ↦ ?_
    rw [assoc, he, assoc, Preadditive.sub_comp, Preadditive.comp_sub, id_comp, ht, he,
      ← assoc, he, ← Hi.map_comp, ← Hi.map_comp, Preadditive.sub_comp, id_comp,
      towerShift_proj, Hi.map_sub, Hi.map_comp]
  have hinv : (𝟙 _ - t) ≫ e.inv = e.inv ≫ Hi.map (𝟙 _ - s) := by
    rw [← cancel_epi e.hom, ← reassoc_of% hcomm, e.hom_inv_id, comp_id, e.hom_inv_id_assoc]
  have hzero : (𝟙 _ - t) ≫ e.inv ≫ δH = 0 := by
    rw [← assoc, hinv, assoc]
    exact (e.inv ≫= HomologySequence.comp_δ _ hT i j hij).trans comp_zero
  have hS₃ : (ShortComplex.mk (𝟙 _ - t) (e.inv ≫ δH) hzero).Exact := by
    refine ShortComplex.exact_of_iso ?_ (HomologySequence.exact₃ _ hT i j hij)
    exact ShortComplex.isoMk e e (Iso.refl _) hcomm.symm (by simp; rfl)
  let a := cokernel.desc _ _ hzero
  have ha : Mono a := hS₃.mono_cokernelDesc
  -- degree `j`: identify the kernel of `Hʲ(1 - t)` with `d.pt`
  let Q : Fan fun n : ℕ ↦ (F ⋙ Hj).obj (op n) := Fan.mk (Hj.obj P'.pt) fun n ↦ Hj.map (P'.proj n)
  let hQ : IsLimit Q := isLimitFanMkObjOfIsLimit Hj _ _ hP'
  have hsQ (n : ℕ) : Hj.map s ≫ Q.proj n = Q.proj (n + 1) ≫ (F ⋙ Hj).map (homOfLE n.le_succ).op :=
    by
      simp only [Q, fan_mk_proj, Functor.comp_map, ← Hj.map_comp, s, towerShift_proj]
  let hk := Fan.IsLimit.isLimitKernelForkOneSub hQ _ hsQ hd
  let m := Fan.IsLimit.lift hQ fun n ↦ d.π.app (op n)
  have hm : Mono m := mono_of_isLimit_fork hk
  let b := hd.lift (Hj.mapCone c)
  have hmπ (n : ℕ) : m ≫ Q.proj n = d.π.app (op n) := Fan.IsLimit.fac hQ _ n
  have hbm : b ≫ m = Hj.map p := Fan.IsLimit.hom_ext hQ _ _ fun n ↦ by
    rw [assoc, hmπ, hd.fac, Functor.mapCone_π_app]
    exact (congrArg Hj.map (hp n).symm).trans (Hj.map_comp _ _)
  have hδp : δH ≫ Hj.map p = 0 := HomologySequence.δ_comp _ hT i j hij
  have hS₁ : (ShortComplex.mk δH (Hj.map p) hδp).Exact := HomologySequence.exact₁ _ hT i j hij
  have hps : Hj.map p ≫ Hj.map (𝟙 _ - s) = 0 := by
    rw [← Hj.map_comp]
    exact (congrArg Hj.map (comp_distTriang_mor_zero₁₂ _ hT)).trans (Hj.map_zero _ _)
  have hS₂ : (ShortComplex.mk (Hj.map p) (Hj.map (𝟙 _ - s)) hps).Exact :=
    HomologySequence.exact₂ _ hT j
  have hpδ : a ≫ Hj.map p = 0 := by
    rw [← cancel_epi (cokernel.π _), cokernel.π_desc_assoc, comp_zero, assoc, hδp, comp_zero]
  have hz : a ≫ b = 0 := by
    rw [← cancel_mono m, assoc, hbm, hpδ, zero_comp]
  refine ⟨a, hz, ShortComplex.ShortExact.mk' ?_ ha ?_⟩
  · have hz' : a ≫ b ≫ m = 0 := by rw [hbm, hpδ]
    let φ : ShortComplex.mk _ _ hδp ⟶ ShortComplex.mk a (b ≫ m) hz' :=
      ShortComplex.homMk (e.hom ≫ cokernel.π _) (𝟙 _) (𝟙 _)
        (by simp [a]) (by simp [hbm])
    have : Epi φ.τ₁ := epi_comp _ _
    have : IsIso φ.τ₂ := inferInstanceAs (IsIso (𝟙 _))
    have : Mono φ.τ₃ := inferInstanceAs (Mono (𝟙 _))
    let ψ : ShortComplex.mk a b hz ⟶ ShortComplex.mk a (b ≫ m) hz' :=
      ShortComplex.homMk (𝟙 _) (𝟙 _) m (by simp) (by simp)
    have : Epi ψ.τ₁ := inferInstanceAs (Epi (𝟙 _))
    have : IsIso ψ.τ₂ := inferInstanceAs (IsIso (𝟙 _))
    have : Mono ψ.τ₃ := hm
    exact (ShortComplex.exact_iff_of_epi_of_isIso_of_mono ψ).2
      ((ShortComplex.exact_iff_of_epi_of_isIso_of_mono φ).1 hS₁)
  · let g : Hj.obj P'.pt ⟶ Hj.obj P'.pt := 𝟙 _ - Hj.map s
    have hg : Hj.map (𝟙 _ - s) = g := by rw [Hj.map_sub, Hj.map_id]
    let φ := hk.conePointUniqueUpToIso (kernelIsKernel g)
    have hφ : φ.hom ≫ kernel.ι g = m :=
      hk.conePointUniqueUpToIso_hom_comp (kernelIsKernel g) WalkingParallelPair.zero
    have hpg : Hj.map p ≫ g = 0 := by rw [← hg, hps]
    have hS₂' : (ShortComplex.mk (Hj.map p) g hpg).Exact :=
      ShortComplex.exact_of_iso (ShortComplex.isoMk (S₁ := ShortComplex.mk _ _ hps)
        (Iso.refl _) (Iso.refl _) (Iso.refl _)
        (by simp) (by simp [hg])) hS₂
    have hlift : kernel.lift g (Hj.map p) hpg = b ≫ φ.hom := by
      rw [← cancel_mono (kernel.ι g), kernel.lift_ι, assoc, hφ, hbm]
    have := hS₂'.epi_kernelLift
    dsimp only at this
    rwa [hlift, epi_comp_iff_of_isIso] at this

/-- **`R¹lim = 0` gives `Hʲ(R lim Fₙ) = lim Hʲ(Fₙ)`.** If, for `i + 1 = j`, the map `1 - t` on a
product of the `Hⁱ(Fₙ)` is an epimorphism (e.g. under the Mittag-Leffler condition), then the
map `Hʲ(c.pt) ⟶ lim Hʲ(Fₙ)` induced by a homotopy limit cone `c` is an isomorphism. -/
theorem isIso_lift_homologyFunctor_mapCone_of_isHomotopyLimit (hc : IsHomotopyLimit c)
    (i j : ℤ) (hij : i + 1 = j) {P : Fan fun n : ℕ ↦ (homologyFunctor C i).obj (F.obj (op n))}
    (hP : IsLimit P) (t : P.pt ⟶ P.pt)
    (ht : ∀ n : ℕ, t ≫ P.proj n =
      P.proj (n + 1) ≫ (homologyFunctor C i).map (F.map (homOfLE n.le_succ).op))
    (hepi : Epi (𝟙 P.pt - t)) {d : Cone (F ⋙ homologyFunctor C j)} (hd : IsLimit d) :
    IsIso (hd.lift ((homologyFunctor C j).mapCone c)) := by
  obtain ⟨a, hz, hS⟩ := shortExact_milnor_of_isHomotopyLimit hc i j hij hP t ht hd
  have : Mono (hd.lift ((homologyFunctor C j).mapCone c)) :=
    (ShortComplex.exact_iff_mono _ ((isZero_cokernel_of_epi _).eq_of_src _ _)).1 hS.exact
  have := hS.epi_g
  exact isIso_of_mono_of_epi _

end DerivedCategory
