/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Sites.CohomologyClopen
public import WeilConjectures.AlgebraicGeometry.Sites.GaGmLowerStar
public import WeilConjectures.CategoryTheory.Sites.CechCriterion
public import WeilConjectures.SixFunctors.Finite.BaseChange

/-!
# `𝔾ₐ` and `𝔾ₘ` along a square-zero closed immersion

Let `h : Z ⟶ Y` be a closed immersion. The kernel `K` of `𝔾ₐ ⟶ h_* 𝔾ₐ` sends an étale `Y`-scheme
`T` to the functions on `T` vanishing on `T ×_Y Z`; it is the étale sheaf of the ideal of `Z`,
and `0 → K → 𝔾ₐ → h_* 𝔾ₐ → 0` is short exact. Since `𝔾ₐ` is acyclic on affine schemes, so is
`K`, in the sense that `Hᵠ(W, w^* K) = 0` for every étale `w : W ⟶ Y` with `W` affine and `q ≥ 1`.

If the ideal of `Z` is of square zero, `a ↦ 1 + a` identifies `K` with the kernel of
`𝔾ₘ ⟶ h_* 𝔾ₘ`, and `𝔾ₘ ⟶ h_* 𝔾ₘ` is an epimorphism, since a function which is a unit modulo a
square-zero ideal is a unit. The long exact cohomology sequence then shows that
`H²(Y, 𝔾ₘ) ⟶ H²(Z, 𝔾ₘ)` is injective as soon as `H²(Y, K) = 0`.

## Main definitions

- `AlgebraicGeometry.Scheme.gaKernel`: the kernel `K` of `𝔾ₐ ⟶ h_* 𝔾ₐ`.

## Main statements

- `AlgebraicGeometry.Scheme.gaKernelSequence_shortExact`: `0 → K → 𝔾ₐ → h_* 𝔾ₐ → 0` is exact.
- `AlgebraicGeometry.Scheme.subsingleton_H_upperStar_gaKernel`: `K` is acyclic on affine étale
  `Y`-schemes.
- `AlgebraicGeometry.Scheme.subsingleton_H_two_gmSheaf_of_squareZero`: `H²(Y, 𝔾ₘ) = 0` if
  `H²(Z, 𝔾ₘ) = 0` and `H²(Y, K) = 0`, for a square-zero closed immersion `h`.
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite

open scoped AlgebraicGeometry.Etale

namespace AlgebraicGeometry.Scheme

/-! ### Global sections over an étale scheme -/

section Transport

variable {X W : Scheme.{u}}

/-- Let `w : W ⟶ X` be étale and `φ : F ⟶ G` a morphism of abelian étale sheaves on `X` which is
surjective on sections over `W`. Then `w^* φ` is surjective on global sections. -/
lemma surjective_app_upperStar_map_of_surjective (w : W ⟶ X) [hw : Etale w]
    {F G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}} (φ : F ⟶ G)
    (hφ : Function.Surjective (φ.hom.app (op (Etale.mk w)))) :
    Function.Surjective (((w)^*[AddCommGrpCat.{u + 1}].map φ).hom.app
      (op (Etale.mk (𝟙 W)))) := by
  let e := Etale.upperStarIsoLocalizationRestriction AddCommGrpCat.{u + 1} w hw
  let O := (MorphismProperty.Over.map ⊤ hw).obj (Etale.mk (𝟙 W))
  let i : O ≅ Etale.mk w := MorphismProperty.Over.isoMk (Iso.refl W) (by simp [O])
  -- `φ` is surjective on sections over `O`
  have hO : Function.Surjective (φ.hom.app (op O)) := by
    intro y
    obtain ⟨x, hx⟩ := hφ (G.obj.map i.inv.op y)
    refine ⟨F.obj.map i.hom.op x, ?_⟩
    rw [NatTrans.naturality_apply, hx, ← ConcreteCategory.comp_apply, ← Functor.map_comp,
      ← op_comp, i.hom_inv_id, op_id, CategoryTheory.Functor.map_id, ConcreteCategory.id_apply]
  intro y
  obtain ⟨x, hx⟩ := hO ((e.hom.app G).hom.app _ y)
  refine ⟨(e.inv.app F).hom.app _ x, ?_⟩
  have h₁ := congrArg (fun ψ ↦ ψ.hom.app (op (Etale.mk (𝟙 W))) x) (e.inv.naturality φ)
  simp only [ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app,
    ConcreteCategory.comp_apply] at h₁
  rw [← h₁]
  change (e.inv.app G).hom.app _ (φ.hom.app (op O) x) = y
  rw [hx]
  change ((e.hom ≫ e.inv).app G).hom.app _ y = y
  rw [e.hom_inv_id]
  rfl

end Transport

variable {Y Z : Scheme.{u}} (h : Z ⟶ Y)

/-! ### The kernel of `𝔾ₐ ⟶ h_* 𝔾ₐ` -/

/-- The kernel `K` of `𝔾ₐ ⟶ h_* 𝔾ₐ`: on an étale `Y`-scheme `T`, the functions on `T` vanishing
on `T ×_Y Z`. For a closed immersion `h` it is the étale sheaf of the ideal of `Z`. -/
noncomputable abbrev gaKernel : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1} :=
  kernel (gaSheafToLowerStarGaSheaf h)

/-- The sequence `0 → K → 𝔾ₐ → h_* 𝔾ₐ`. -/
noncomputable def gaKernelSequence :
    ShortComplex (Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}) :=
  ShortComplex.mk (kernel.ι (gaSheafToLowerStarGaSheaf h)) (gaSheafToLowerStarGaSheaf h)
    (kernel.condition _)

/-- An étale `Y`-scheme is covered by affine étale `Y`-schemes: every point of `V` lies in an
affine open `A` of `V`, which is étale over `Y`. -/
lemma exists_affine_etale_mem (V : Y.Etale) (x : V.left) :
    ∃ (A : V.left.Opens) (_ : IsAffineOpen A), x ∈ A := by
  obtain ⟨A, hA, hxA, -⟩ : ∃ A : V.left.Opens, A ∈ V.left.affineOpens ∧ x ∈ A ∧ A ≤ ⊤ :=
    (TopologicalSpace.Opens.isBasis_iff_nbhd.1 V.left.isBasis_affineOpens)
      (TopologicalSpace.Opens.mem_top x)
  exact ⟨A, hA, hxA⟩

/-- The affine open `A` of an étale `Y`-scheme `V`, as an étale `Y`-scheme. -/
noncomputable abbrev etaleOfOpens (V : Y.Etale) (A : V.left.Opens) : Y.Etale :=
  MorphismProperty.Over.mk ⊤ (A.ι ≫ V.hom) (MorphismProperty.comp_mem _ _ _ inferInstance V.prop)

/-- The inclusion of `etaleOfOpens V A` into `V`. -/
noncomputable abbrev etaleOfOpensι (V : Y.Etale) (A : V.left.Opens) : etaleOfOpens V A ⟶ V :=
  MorphismProperty.Over.homMk A.ι rfl trivial

/-- For a closed immersion `h`, the map `𝔾ₐ ⟶ h_* 𝔾ₐ` is surjective on affine étale
`Y`-schemes, hence locally surjective. -/
theorem isLocallySurjective_gaSheafToLowerStarGaSheaf [IsClosedImmersion h] :
    Sheaf.IsLocallySurjective (gaSheafToLowerStarGaSheaf h) where
  imageSieve_mem {V} s := by
    refine (Scheme.mem_smallEtaleTopology_iff _).2 fun x ↦ ?_
    obtain ⟨A, hA, hxA⟩ := exists_affine_etale_mem V x
    have : IsAffine A := hA
    refine ⟨etaleOfOpens V A, etaleOfOpensι V A, ?_, ⟨x, hxA⟩, rfl⟩
    obtain ⟨a, ha⟩ := (IsClosedImmersion.isAffine_surjective_of_isAffine
      (pullback.fst (A.ι ≫ V.hom) h)).2
      ((((Etale.lowerStar AddCommGrpCat.{u + 1} h).obj Z.gaSheaf).obj.map
        (etaleOfOpensι V A).op s).down)
    exact ⟨ULift.up a, ULift.ext ha⟩

/-- **The ideal sequence.** For a closed immersion `h : Z ⟶ Y`, the sequence
`0 → K → 𝔾ₐ → h_* 𝔾ₐ → 0` of étale sheaves on `Y` is short exact. -/
theorem gaKernelSequence_shortExact [IsClosedImmersion h] : (gaKernelSequence h).ShortExact :=
  have := isLocallySurjective_gaSheafToLowerStarGaSheaf h
  { exact := ShortComplex.exact_of_f_is_kernel _ (kernelIsKernel _)
    mono_f := by dsimp [gaKernelSequence]; infer_instance
    epi_g := Sheaf.epi_of_isLocallySurjective (gaSheafToLowerStarGaSheaf h) }

/-- The sections of `K` vanish on `T ×_Y Z`. -/
lemma appTop_kernelι_gaSheafToLowerStarGaSheaf (T : Y.Etale)
    (x : (gaKernel h).obj.obj (op T)) :
    (pullback.fst T.hom h).appTop
      ((kernel.ι (gaSheafToLowerStarGaSheaf h)).hom.app (op T) x).down = 0 :=
  congrArg ULift.down (Sheaf.app_g_app_f (S := gaKernelSequence h) (op T) x)

/-- **`K` is acyclic on affine étale `Y`-schemes.** Let `h : Z ⟶ Y` be a closed immersion and
`w : W ⟶ Y` étale with `W` affine. Then `Hᵠ(W, w^* K) = 0` for `q ≥ 1`: in the long exact
sequence of `0 → w^* K → w^* 𝔾ₐ → w^* h_* 𝔾ₐ → 0`, the sheaf `w^* 𝔾ₐ = 𝔾ₐ` is acyclic on the
affine `W`, the sheaf `w^* h_* 𝔾ₐ = h'_* 𝔾ₐ` is acyclic since `h' : W ×_Y Z ⟶ W` is finite and
`W ×_Y Z` is affine, and `𝔾ₐ(W) ⟶ 𝔾ₐ(W ×_Y Z)` is surjective. -/
theorem subsingleton_H_upperStar_gaKernel [IsClosedImmersion h] {W : Scheme.{u}} (w : W ⟶ Y)
    [Etale w] [IsAffine W] (q : ℕ) :
    Subsingleton (Sheaf.H ((w)^*[AddCommGrpCat.{u + 1}].obj (gaKernel h)) (q + 1)) := by
  let P := (w)^*[AddCommGrpCat.{u + 1}]
  have hS := (gaKernelSequence_shortExact h).map_of_exact P
  -- `w^* 𝔾ₐ = 𝔾ₐ` is acyclic
  have h₂ (n : ℕ) : Subsingleton (Sheaf.H ((gaKernelSequence h).map P).X₂ (n + 1)) :=
    have : Subsingleton ((Sheaf.functorH _ (n + 1)).obj W.gaSheaf) :=
      subsingleton_sheafH_gaSheaf_of_isAffine W n
    ((Sheaf.functorH _ (n + 1)).mapIso
      (upperStarGaSheafIso w)).addCommGroupIsoToAddEquiv.toEquiv.subsingleton
  -- `w^* h_* 𝔾ₐ = h'_* 𝔾ₐ` is acyclic
  have h₃ (n : ℕ) : Subsingleton (Sheaf.H ((gaKernelSequence h).map P).X₃ (n + 1)) := by
    have sq := (IsPullback.of_hasPullback w h).flip
    have := Etale.isIso_baseChangeMap_of_isFinite AddCommGrpCat.{u + 1} sq
    let e := asIso ((Etale.baseChangeMap AddCommGrpCat.{u + 1} sq.toCommSq).app Z.gaSheaf)
    have : Subsingleton (Sheaf.H ((𝟭 (Sheaf (pullback w h).smallEtaleTopology
        AddCommGrpCat.{u + 1})).obj ((pullback.snd w h)^*[AddCommGrpCat.{u + 1}].obj
          Z.gaSheaf)) (n + 1)) :=
      have : Subsingleton ((Sheaf.functorH _ (n + 1)).obj (pullback w h).gaSheaf) :=
        subsingleton_sheafH_gaSheaf_of_isAffine (pullback w h) n
      ((Sheaf.functorH _ (n + 1)).mapIso
        (upperStarGaSheafIso (pullback.snd w h))).addCommGroupIsoToAddEquiv.toEquiv.subsingleton
    have : Subsingleton ((Sheaf.functorH _ (n + 1)).obj
        (((pullback.snd w h)^*[AddCommGrpCat.{u + 1}] ⋙
          ((pullback.fst w h))_*[AddCommGrpCat.{u + 1}]).obj Z.gaSheaf)) :=
      (Etale.bijective_edgeMap_of_isFinite (pullback.fst w h) _ (n + 1)).injective.subsingleton
    exact ((Sheaf.functorH _ (n + 1)).mapIso e).addCommGroupIsoToAddEquiv.toEquiv.subsingleton
  rcases q with _ | q
  · -- `H¹`: global sections of `w^* h_* 𝔾ₐ` lift
    have hT := MorphismProperty.Over.mkIdTerminal @Etale W
    have hsurj : Function.Surjective (((gaKernelSequence h).map P).g.hom.app
        (op (Etale.mk (𝟙 W)))) := by
      refine surjective_app_upperStar_map_of_surjective w _ ?_
      intro s
      obtain ⟨a, ha⟩ := (IsClosedImmersion.isAffine_surjective_of_isAffine
        (pullback.fst w h)).2 s.down
      exact ⟨ULift.up a, ULift.ext ha⟩
    refine subsingleton_of_forall_eq 0 fun x ↦ ?_
    obtain ⟨s, rfl⟩ := (Sheaf.H.exact_δ_map hS hT x).1 (Subsingleton.elim _ _)
    obtain ⟨t, ht⟩ := hsurj s
    have : s ∈ (Sheaf.H.δSections hS hT).ker := by
      rw [Sheaf.H.ker_δ]
      exact ⟨t, ht⟩
    exact this
  · refine subsingleton_of_forall_eq 0 fun x ↦ ?_
    obtain ⟨y, rfl⟩ := (Sheaf.H.exact_δSucc_map hS (q + 1) x).1 (Subsingleton.elim _ _)
    rw [Subsingleton.elim y 0, map_zero]

/-! ### Square-zero closed immersions and `𝔾ₘ` -/

/-- The unit `1 + a` of a commutative ring, for `a` of square zero. -/
def unitsOneAddOfMulSelf {R : Type*} [CommRing R] (a : R) (ha : a * a = 0) : Rˣ where
  val := 1 + a
  inv := 1 - a
  val_inv := by linear_combination -ha
  inv_val := by linear_combination -ha

@[simp]
lemma val_unitsOneAddOfMulSelf {R : Type*} [CommRing R] (a : R) (ha : a * a = 0) :
    (unitsOneAddOfMulSelf a ha : R) = 1 + a :=
  rfl

/-- The function on `T` underlying a section of `K` over `T`. -/
noncomputable def gaKernelVal (T : Y.Etaleᵒᵖ) (x : (gaKernel h).obj.obj T) : Γ(T.unop.left, ⊤) :=
  ((kernel.ι (gaSheafToLowerStarGaSheaf h)).hom.app T x).down

lemma gaKernelVal_add (T : Y.Etaleᵒᵖ) (x y : (gaKernel h).obj.obj T) :
    gaKernelVal h T (x + y) = gaKernelVal h T x + gaKernelVal h T y := by
  simp only [gaKernelVal, map_add]
  rfl

lemma gaKernelVal_zero (T : Y.Etaleᵒᵖ) : gaKernelVal h T 0 = 0 := by
  simp only [gaKernelVal, map_zero]
  rfl

lemma gaKernelVal_injective (T : Y.Etaleᵒᵖ) [IsClosedImmersion h] :
    Function.Injective (gaKernelVal h T) := fun _ _ hxy ↦
  Sheaf.injective_app_f (gaKernelSequence_shortExact h) T (ULift.ext hxy)

lemma gaKernelVal_map {T T' : Y.Etaleᵒᵖ} (g : T ⟶ T') (x : (gaKernel h).obj.obj T) :
    gaKernelVal h T' ((gaKernel h).obj.map g x) = g.unop.left.appTop (gaKernelVal h T x) := by
  simp only [gaKernelVal, NatTrans.naturality_apply]
  rfl

/-- The sections of `K` vanish on `T ×_Y Z`. -/
lemma appTop_gaKernelVal (T : Y.Etaleᵒᵖ) (x : (gaKernel h).obj.obj T) :
    (pullback.fst T.unop.hom h).appTop (gaKernelVal h T x) = 0 :=
  appTop_kernelι_gaSheafToLowerStarGaSheaf h T.unop x

/-- The functions on `T` vanishing on `T ×_Y Z` are the sections of `K`. -/
lemma exists_gaKernelVal_eq [IsClosedImmersion h] (T : Y.Etaleᵒᵖ) (a : Γ(T.unop.left, ⊤))
    (ha : (pullback.fst T.unop.hom h).appTop a = 0) : ∃ x, gaKernelVal h T x = a := by
  obtain ⟨x, hx⟩ := Sheaf.exists_app_f_eq (gaKernelSequence_shortExact h) T (ULift.up a)
    (ULift.ext ha)
  exact ⟨x, congrArg ULift.down hx⟩

/-- The unit underlying a section of `𝔾ₘ`. -/
noncomputable def gmVal {X : Scheme.{u}} (T : X.Etaleᵒᵖ) (x : X.gmSheaf.obj.obj T) :
    Γ(T.unop.left, ⊤)ˣ :=
  Additive.toMul x.down

/-- A unit of `Γ(T, 𝒪)` as a section of `𝔾ₘ`. -/
noncomputable def gmMk {X : Scheme.{u}} (T : X.Etaleᵒᵖ) (v : Γ(T.unop.left, ⊤)ˣ) :
    X.gmSheaf.obj.obj T :=
  ULift.up (Additive.ofMul v)

lemma gmVal_injective {X : Scheme.{u}} (T : X.Etaleᵒᵖ) : Function.Injective (gmVal T) :=
  fun _ _ hxy ↦ ULift.ext (Additive.toMul.injective hxy)

/-- On sections, `𝔾ₘ ⟶ h_* 𝔾ₘ` is pullback of functions along `T ×_Y Z ⟶ T`. -/
lemma val_gmSheafToLowerStarGmSheaf_app (T : Y.Etaleᵒᵖ) (x : Y.gmSheaf.obj.obj T) :
    ((Additive.toMul ((gmSheafToLowerStarGmSheaf h).hom.app T x).down :
      Γ(pullback T.unop.hom h, ⊤)ˣ) : Γ(pullback T.unop.hom h, ⊤)) =
      (pullback.fst T.unop.hom h).appTop (gmVal T x : Γ(T.unop.left, ⊤)) :=
  rfl

/-- The sequence `0 → 𝔾ₘ' → 𝔾ₘ → h_* 𝔾ₘ`, with `𝔾ₘ'` the kernel. -/
noncomputable def gmKernelSequence :
    ShortComplex (Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}) :=
  ShortComplex.mk (kernel.ι (gmSheafToLowerStarGmSheaf h)) (gmSheafToLowerStarGmSheaf h)
    (kernel.condition _)

variable {h}

section SquareZero

variable (hsq : ∀ (T : Y.Etale) (a b : Γ(T.left, ⊤)), (pullback.fst T.hom h).appTop a = 0 →
  (pullback.fst T.hom h).appTop b = 0 → a * b = 0)

include hsq

/-- For a square-zero closed immersion `h`, the map `𝔾ₘ ⟶ h_* 𝔾ₘ` is surjective on affine étale
`Y`-schemes, since a function which is a unit modulo a square-zero ideal is a unit; hence it is
locally surjective. -/
theorem isLocallySurjective_gmSheafToLowerStarGmSheaf [IsClosedImmersion h] :
    Sheaf.IsLocallySurjective (gmSheafToLowerStarGmSheaf h) where
  imageSieve_mem {V} s := by
    refine (Scheme.mem_smallEtaleTopology_iff _).2 fun x ↦ ?_
    obtain ⟨A, hA, hxA⟩ := exists_affine_etale_mem V x
    have : IsAffine A := hA
    refine ⟨etaleOfOpens V A, etaleOfOpensι V A, ?_, ⟨x, hxA⟩, rfl⟩
    let s' := (((Etale.lowerStar AddCommGrpCat.{u + 1} h).obj Z.gmSheaf).obj.map
      (etaleOfOpensι V A).op s)
    let v : Γ(pullback (A.ι ≫ V.hom) h, ⊤)ˣ := Additive.toMul s'.down
    have hsurj := (IsClosedImmersion.isAffine_surjective_of_isAffine
      (pullback.fst (A.ι ≫ V.hom) h)).2
    obtain ⟨a, ha⟩ := hsurj (v : Γ(pullback (A.ι ≫ V.hom) h, ⊤))
    obtain ⟨b, hb⟩ := hsurj (↑v⁻¹ : Γ(pullback (A.ι ≫ V.hom) h, ⊤))
    have hc : (pullback.fst (A.ι ≫ V.hom) h).appTop (a * b - 1) = 0 := by
      rw [map_sub, map_mul, map_one, ha, hb, Units.mul_inv, sub_self]
    have hcc := hsq (etaleOfOpens V A) _ _ hc hc
    let ua : Γ(A, ⊤)ˣ :=
      { val := a
        inv := b * (1 - (a * b - 1))
        val_inv := by linear_combination -hcc
        inv_val := by linear_combination -hcc }
    exact ⟨ULift.up (Additive.ofMul ua), ULift.ext (Additive.toMul.injective (Units.ext ha))⟩

theorem gmKernelSequence_shortExact [IsClosedImmersion h] : (gmKernelSequence h).ShortExact :=
  have := isLocallySurjective_gmSheafToLowerStarGmSheaf hsq
  { exact := ShortComplex.exact_of_f_is_kernel _ (kernelIsKernel _)
    mono_f := by dsimp [gmKernelSequence]; infer_instance
    epi_g := Sheaf.epi_of_isLocallySurjective (gmSheafToLowerStarGmSheaf h) }

lemma gaKernelVal_mul_self (T : Y.Etaleᵒᵖ) (x y : (gaKernel h).obj.obj T) :
    gaKernelVal h T x * gaKernelVal h T y = 0 :=
  hsq T.unop _ _ (appTop_gaKernelVal h T x) (appTop_gaKernelVal h T y)

/-- The map `K ⟶ 𝔾ₘ`, `a ↦ 1 + a`, for a square-zero closed immersion. -/
noncomputable def gaKernelToGmSheaf : gaKernel h ⟶ Y.gmSheaf where
  hom :=
    { app T := AddCommGrpCat.ofHom
        { toFun x := gmMk T (unitsOneAddOfMulSelf (gaKernelVal h T x)
            (gaKernelVal_mul_self hsq T x x))
          map_zero' := gmVal_injective T (Units.ext (by
            change 1 + gaKernelVal h T 0 = 1
            rw [gaKernelVal_zero, add_zero]))
          map_add' x y := gmVal_injective T (Units.ext (by
            change 1 + gaKernelVal h T (x + y) =
              (1 + gaKernelVal h T x) * (1 + gaKernelVal h T y)
            rw [gaKernelVal_add]
            linear_combination -gaKernelVal_mul_self hsq T x y)) }
      naturality T T' g := by
        ext x
        refine gmVal_injective T' (Units.ext ?_)
        change 1 + gaKernelVal h T' ((gaKernel h).obj.map g x) =
          g.unop.left.appTop (1 + gaKernelVal h T x)
        rw [gaKernelVal_map, map_add, map_one] }

lemma val_gaKernelToGmSheaf_app (T : Y.Etaleᵒᵖ) (x : (gaKernel h).obj.obj T) :
    (gmVal T ((gaKernelToGmSheaf hsq).hom.app T x) : Γ(T.unop.left, ⊤)) =
      (1 : Γ(T.unop.left, ⊤)) + gaKernelVal h T x :=
  rfl

/-- `K` maps to the kernel of `𝔾ₘ ⟶ h_* 𝔾ₘ`. -/
lemma gaKernelToGmSheaf_comp : gaKernelToGmSheaf hsq ≫ gmSheafToLowerStarGmSheaf h = 0 := by
  apply Sheaf.hom_ext
  ext T x
  refine ULift.ext (Additive.toMul.injective (Units.ext ?_))
  change (pullback.fst T.unop.hom h).appTop ((1 : Γ(T.unop.left, ⊤)) + gaKernelVal h T x) = 1
  rw [map_add, map_one, appTop_gaKernelVal h T x, add_zero]

/-- **`a ↦ 1 + a` identifies `K` with the kernel of `𝔾ₘ ⟶ h_* 𝔾ₘ`.** -/
theorem isIso_kernelLift_gaKernelToGmSheaf [IsClosedImmersion h] :
    IsIso (kernel.lift _ _ (gaKernelToGmSheaf_comp hsq)) := by
  have hSm := gmKernelSequence_shortExact hsq
  let φ := kernel.lift _ _ (gaKernelToGmSheaf_comp hsq)
  have hφ : φ ≫ kernel.ι _ = gaKernelToGmSheaf hsq := kernel.lift_ι _ _ _
  have happ (T : Y.Etaleᵒᵖ) (x : (gaKernel h).obj.obj T) :
      (kernel.ι (gmSheafToLowerStarGmSheaf h)).hom.app T (φ.hom.app T x) =
        (gaKernelToGmSheaf hsq).hom.app T x := by
    rw [← hφ]
    rfl
  suffices ∀ T, IsIso (φ.hom.app T) by
    have : ∀ T, IsIso (((sheafToPresheaf _ _).map φ).app T) := this
    have : IsIso ((sheafToPresheaf _ _).map φ) := NatIso.isIso_of_isIso_app _
    exact isIso_of_reflects_iso _ (sheafToPresheaf _ _)
  intro T
  rw [ConcreteCategory.isIso_iff_bijective]
  refine ⟨fun x y hxy ↦ ?_, fun y ↦ ?_⟩
  · have h₁ := congrArg (fun z ↦ (gmVal T
      ((kernel.ι (gmSheafToLowerStarGmSheaf h)).hom.app T z) : Γ(T.unop.left, ⊤))) hxy
    simp only [happ, val_gaKernelToGmSheaf_app, add_right_inj] at h₁
    exact gaKernelVal_injective h T h₁
  · let u := (kernel.ι (gmSheafToLowerStarGmSheaf h)).hom.app T y
    have hu : (gmSheafToLowerStarGmSheaf h).hom.app T u = 0 :=
      Sheaf.app_g_app_f (S := gmKernelSequence h) T y
    have hu' : (pullback.fst T.unop.hom h).appTop (gmVal T u : Γ(T.unop.left, ⊤)) = 1 :=
      (val_gmSheafToLowerStarGmSheaf_app h T u).symm.trans
        (congrArg (fun z ↦ ((Additive.toMul z.down : Γ(pullback T.unop.hom h, ⊤)ˣ) :
          Γ(pullback T.unop.hom h, ⊤))) hu)
    obtain ⟨x, hx⟩ := exists_gaKernelVal_eq h T ((gmVal T u : Γ(T.unop.left, ⊤)) - 1)
      (by rw [map_sub, map_one, hu', sub_self])
    refine ⟨x, Sheaf.injective_app_f hSm T ?_⟩
    change (kernel.ι (gmSheafToLowerStarGmSheaf h)).hom.app T (φ.hom.app T x) = u
    rw [happ]
    refine gmVal_injective T (Units.ext ?_)
    rw [val_gaKernelToGmSheaf_app, hx]
    exact add_sub_cancel _ _

/-- **`𝔾ₘ` along a square-zero closed immersion.** Let `h : Z ⟶ Y` be a closed immersion whose
ideal is of square zero, in the sense that any two functions on an étale `Y`-scheme `T` which
vanish on `T ×_Y Z` have product zero. If `H²(Y, K) = 0` for the ideal sheaf `K` and
`H²(Z, 𝔾ₘ) = 0`, then `H²(Y, 𝔾ₘ) = 0`: the kernel of `𝔾ₘ ⟶ h_* 𝔾ₘ` is isomorphic to `K` via
`a ↦ 1 + a`, and `H²(Y, h_* 𝔾ₘ) = H²(Z, 𝔾ₘ)` since `h` is finite. -/
theorem subsingleton_H_two_gmSheaf_of_squareZero [IsClosedImmersion h]
    (hK : Subsingleton (Sheaf.H (gaKernel h) 2))
    (hZ : Subsingleton (Sheaf.H Z.gmSheaf 2)) : Subsingleton (Sheaf.H Y.gmSheaf 2) := by
  have hSm := gmKernelSequence_shortExact hsq
  have := isIso_kernelLift_gaKernelToGmSheaf hsq
  have : Subsingleton ((Sheaf.functorH _ 2).obj (gaKernel h)) := hK
  have h₁ : Subsingleton (Sheaf.H (gmKernelSequence h).X₁ 2) :=
    ((Sheaf.functorH _ 2).mapIso (asIso (kernel.lift _ _
      (gaKernelToGmSheaf_comp hsq)))).addCommGroupIsoToAddEquiv.symm.toEquiv.subsingleton
  have h₃ : Subsingleton (Sheaf.H (gmKernelSequence h).X₃ 2) :=
    have : Subsingleton (Sheaf.H ((𝟭 (Sheaf Z.smallEtaleTopology
        AddCommGrpCat.{u + 1})).obj Z.gmSheaf) 2) := hZ
    (Etale.bijective_edgeMap_of_isFinite h _ 2).injective.subsingleton
  refine subsingleton_of_forall_eq 0 fun x ↦ ?_
  obtain ⟨y, rfl⟩ := (Sheaf.H.exact_map_map hSm 2 x).1 (Subsingleton.elim _ _)
  rw [Subsingleton.elim y 0, map_zero]

end SquareZero

end AlgebraicGeometry.Scheme
