/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.FlatModel
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor

/-!
# Chain-level models of derived base change

Let `res : 𝒜' ⥤ 𝒜` be an exact, fully faithful functor between abelian categories (the
restriction of scalars along a surjective ring morphism `A ⟶ A'`) and `σ` an endomorphism of
the identity functor of `𝒜` (the multiplication by a generator `a` of the kernel). A
*reduction datum* (`CategoryTheory.Functor.ReductionDatum`) is a functor `Φ : 𝒜 ⥤ 𝒜'` (the
extension of scalars `- ⊗_A A'`) with a natural epimorphism `r : F ⟶ res Φ(F)` whose kernel is
the image of `σ`, such that `Φ` sends quasi-isomorphisms between K-flat complexes to
quasi-isomorphisms.

For a K-flat complex `P`, the reduction `Q P ⟶ res Q Φ(P)` is then a universal arrow from
`Q P` to the derived functor `res : D(𝒜') ⥤ D(𝒜)`
(`CategoryTheory.Functor.ReductionDatum.bijective_comp_map`): it exhibits `Φ(P)` as the
derived base change of `P`.

The proof is elementary. A morphism `Q P ⟶ res M` is a fraction `inv (Q s) ≫ Q g` with
`s : X ⟶ P` a quasi-isomorphism, which may be taken from a K-flat complex; then `g` factors
through the reduction of `X`, and `Φ(s)` is a quasi-isomorphism. A morphism
`h : Q Φ(P) ⟶ M` killed by the reduction is a fraction `Q w ≫ inv (Q s)`; pulling back the
reduction of `P` along `s` and resolving gives a K-flat complex `V` with a quasi-isomorphism to
`P` through which `h` becomes the image of a chain map that is null-homotopic after reduction,
and homotopies descend along the epimorphism `r`.
-/

@[expose] public section

open CategoryTheory Limits

namespace DerivedCategory

variable {C : Type*} [Category C] [Abelian C] [HasDerivedCategory C]

set_option backward.isDefEq.respectTransparency.types false in
/-- A morphism of complexes which becomes zero in the derived category is null-homotopic after
precomposition with a quasi-isomorphism. -/
lemma exists_quasiIso_homotopy_zero_of_Q_map_eq_zero {K L : CochainComplex C ℤ} (x : K ⟶ L)
    (hx : Q.map x = 0) :
    ∃ (Z : CochainComplex C ℤ) (u : Z ⟶ K), QuasiIso u ∧ Nonempty (Homotopy (u ≫ x) 0) := by
  have h : Qh.map ((HomotopyCategory.quotient _ _).map x) = Qh.map 0 := by
    rw [← cancel_mono ((quotientCompQhIso C).hom.app L), quotientCompQhIso_hom_naturality, hx]
    simp
  rw [MorphismProperty.map_eq_iff_precomp Qh (HomotopyCategory.quasiIso C _)] at h
  obtain ⟨X, s, hs, h⟩ := h
  obtain ⟨Z, rfl⟩ := HomotopyCategory.quotient_obj_surjective X
  obtain ⟨u, rfl⟩ := (HomotopyCategory.quotient _ _).map_surjective s
  rw [HomotopyCategory.quotient_map_mem_quasiIso_iff] at hs
  refine ⟨Z, u, hs, ⟨HomotopyCategory.homotopyOfEq _ _ ?_⟩⟩
  simpa using h

end DerivedCategory

namespace CategoryTheory.Functor

section

variable {C₁ C₂ : Type*} [Category C₁] [Abelian C₁] [HasDerivedCategory C₁]
  [Category C₂] [Abelian C₂] [HasDerivedCategory C₂]
  (F : C₁ ⥤ C₂) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]

/-- The naturality of the inverse of `F.mapDerivedCategoryFactors`. -/
@[reassoc]
lemma mapDerivedCategoryFactors_inv_naturality {K L : CochainComplex C₁ ℤ} (a : K ⟶ L) :
    DerivedCategory.Q.map ((F.mapHomologicalComplex (.up ℤ)).map a) ≫
        F.mapDerivedCategoryFactors.inv.app L =
      F.mapDerivedCategoryFactors.inv.app K ≫
        F.mapDerivedCategory.map (DerivedCategory.Q.map a) :=
  F.mapDerivedCategoryFactors.inv.naturality a

/-- Conjugating `F.mapDerivedCategory.map (Q.map a)` by `F.mapDerivedCategoryFactors` gives
`Q.map` of the image of `a`. -/
@[reassoc]
lemma mapDerivedCategoryFactors_inv_app_comp_map_comp_hom_app {K L : CochainComplex C₁ ℤ}
    (a : K ⟶ L) :
    F.mapDerivedCategoryFactors.inv.app K ≫ F.mapDerivedCategory.map (DerivedCategory.Q.map a) ≫
        F.mapDerivedCategoryFactors.hom.app L =
      DerivedCategory.Q.map ((F.mapHomologicalComplex (.up ℤ)).map a) := by
  rw [mapDerivedCategoryFactors_hom_naturality, Iso.inv_hom_id_app_assoc]

end

variable {𝒜 𝒜' : Type*} [Category 𝒜] [Abelian 𝒜] [IsGrothendieckAbelian.{v} 𝒜]
  [MonoidalCategory 𝒜] [MonoidalPreadditive 𝒜] [MonoidalClosed 𝒜] [BraidedCategory 𝒜]
  [Abelian.HasFunctorialFlatResolution 𝒜] [HasDerivedCategory 𝒜]
  [Category 𝒜'] [Abelian 𝒜'] [HasDerivedCategory 𝒜']
  (res : 𝒜' ⥤ 𝒜) [res.Additive] [PreservesFiniteLimits res] [PreservesFiniteColimits res]
  (σ : 𝟭 𝒜 ⟶ 𝟭 𝒜)

/-- A chain-level model of derived base change along `res`: a functor `Φ : 𝒜 ⥤ 𝒜'` with a
natural epimorphism `r : F ⟶ res Φ(F)` whose kernel is the image of `σ`, such that `Φ` sends
quasi-isomorphisms between K-flat complexes to quasi-isomorphisms. The endomorphism `σ` is
required to vanish on the image of `res`. -/
structure ReductionDatum where
  /-- The reduction functor. -/
  Φ : 𝒜 ⥤ 𝒜'
  [additive : Φ.Additive]
  /-- The reduction map `F ⟶ res Φ(F)`. -/
  r : 𝟭 𝒜 ⟶ Φ ⋙ res
  /-- The endomorphism `σ` vanishes on the image of `res`. -/
  σ_app_obj (X : 𝒜') : σ.app (res.obj X) = 0
  σ_comp_r (F : 𝒜) : σ.app F ≫ r.app F = 0
  epi_r (F : 𝒜) : Epi (r.app F)
  exact (F : 𝒜) : (ShortComplex.mk _ _ (σ_comp_r F)).Exact
  quasiIso_map {P₁ P₂ : CochainComplex 𝒜 ℤ} (φ : P₁ ⟶ P₂) [QuasiIso φ]
    (h₁ : (HomologicalComplex.quasiIso 𝒜 (.up ℤ)).kFlat P₁)
    (h₂ : (HomologicalComplex.quasiIso 𝒜 (.up ℤ)).kFlat P₂) :
    QuasiIso ((Φ.mapHomologicalComplex (.up ℤ)).map φ)

attribute [instance] ReductionDatum.additive

namespace ReductionDatum

variable {res σ} (D : ReductionDatum res σ)

/-- The reduction `P ⟶ res Φ(P)` of a complex. -/
@[simps]
def complexMap (P : CochainComplex 𝒜 ℤ) :
    P ⟶ (res.mapHomologicalComplex (.up ℤ)).obj ((D.Φ.mapHomologicalComplex (.up ℤ)).obj P) where
  f i := D.r.app (P.X i)
  comm' _ _ _ := (D.r.naturality _).symm

omit [Abelian.HasFunctorialFlatResolution 𝒜] [HasDerivedCategory 𝒜] [HasDerivedCategory 𝒜']
  [PreservesFiniteLimits res] [PreservesFiniteColimits res] in
/-- The reduction of complexes is natural. -/
@[reassoc]
lemma complexMap_naturality {P P' : CochainComplex 𝒜 ℤ} (f : P ⟶ P') :
    f ≫ D.complexMap P' =
      D.complexMap P ≫ (res.mapHomologicalComplex (.up ℤ)).map
        ((D.Φ.mapHomologicalComplex (.up ℤ)).map f) := by
  ext i
  exact D.r.naturality (f.f i)

/-- A morphism `X ⟶ res Y` descends along the reduction `X ⟶ res Φ(X)`. -/
noncomputable def desc [res.Full] {X : 𝒜} {Y : 𝒜'} (g : X ⟶ res.obj Y) : D.Φ.obj X ⟶ Y :=
  haveI := D.epi_r X
  res.preimage ((D.exact X).desc g (by
    have := σ.naturality g
    dsimp at this ⊢
    rw [← this, D.σ_app_obj, Limits.comp_zero]))

omit [Abelian.HasFunctorialFlatResolution 𝒜] [HasDerivedCategory 𝒜] [HasDerivedCategory 𝒜']
  [res.Additive] [PreservesFiniteLimits res] [PreservesFiniteColimits res] in
/-- The defining property of `ReductionDatum.desc`. -/
@[reassoc (attr := simp)]
lemma r_app_comp_map_desc [res.Full] {X : 𝒜} {Y : 𝒜'} (g : X ⟶ res.obj Y) :
    D.r.app X ≫ res.map (D.desc g) = g := by
  have := D.epi_r X
  simp only [desc, Functor.map_preimage]
  exact (D.exact X).g_desc _ _

omit [Abelian.HasFunctorialFlatResolution 𝒜] [HasDerivedCategory 𝒜] [HasDerivedCategory 𝒜']
  [res.Additive] [PreservesFiniteLimits res] [PreservesFiniteColimits res] in
/-- Two morphisms out of `Φ(X)` agree as soon as they agree after restriction and composition
with the reduction. -/
lemma hom_ext [res.Faithful] {X : 𝒜} {Y : 𝒜'} {a b : D.Φ.obj X ⟶ Y}
    (h : D.r.app X ≫ res.map a = D.r.app X ≫ res.map b) : a = b := by
  have := D.epi_r X
  exact res.map_injective ((cancel_epi _).1 h)

/-- A morphism of complexes `P ⟶ res M` descends along the reduction of `P`. -/
@[simps]
noncomputable def descComplex [res.Full] [res.Faithful] {P : CochainComplex 𝒜 ℤ}
    {M : CochainComplex 𝒜' ℤ} (g : P ⟶ (res.mapHomologicalComplex (.up ℤ)).obj M) :
    (D.Φ.mapHomologicalComplex (.up ℤ)).obj P ⟶ M where
  f i := D.desc (g.f i)
  comm' i j _ := by
    refine D.hom_ext ?_
    have h₁ := D.r_app_comp_map_desc (g.f i)
    have h₂ := D.r_app_comp_map_desc (g.f j)
    have hr := D.r.naturality (P.d i j)
    have hg := g.comm i j
    dsimp at h₁ h₂ hr hg ⊢
    rw [Functor.map_comp, Functor.map_comp, reassoc_of% h₁]
    erw [← reassoc_of% hr, h₂]
    exact hg

omit [Abelian.HasFunctorialFlatResolution 𝒜] [HasDerivedCategory 𝒜] [HasDerivedCategory 𝒜']
  [PreservesFiniteLimits res] [PreservesFiniteColimits res] in
/-- The defining property of `ReductionDatum.descComplex`. -/
@[reassoc (attr := simp)]
lemma complexMap_comp_descComplex [res.Full] [res.Faithful] {P : CochainComplex 𝒜 ℤ}
    {M : CochainComplex 𝒜' ℤ} (g : P ⟶ (res.mapHomologicalComplex (.up ℤ)).obj M) :
    D.complexMap P ≫ (res.mapHomologicalComplex (.up ℤ)).map (D.descComplex g) = g := by
  ext i
  simp

omit [Abelian.HasFunctorialFlatResolution 𝒜] [HasDerivedCategory 𝒜] [HasDerivedCategory 𝒜']
  [PreservesFiniteLimits res] [PreservesFiniteColimits res] in
/-- Two morphisms out of `Φ(P)` agree as soon as they agree after restriction and composition
with the reduction of `P`. -/
lemma complexMap_ext [res.Faithful] {P : CochainComplex 𝒜 ℤ} {M : CochainComplex 𝒜' ℤ}
    {a b : (D.Φ.mapHomologicalComplex (.up ℤ)).obj P ⟶ M}
    (h : D.complexMap P ≫ (res.mapHomologicalComplex (.up ℤ)).map a =
      D.complexMap P ≫ (res.mapHomologicalComplex (.up ℤ)).map b) : a = b := by
  ext i
  exact D.hom_ext (by simpa using HomologicalComplex.congr_hom h i)

omit [Abelian.HasFunctorialFlatResolution 𝒜] [HasDerivedCategory 𝒜] [HasDerivedCategory 𝒜']
  [PreservesFiniteLimits res] [PreservesFiniteColimits res] in
/-- Every morphism of complexes `P ⟶ res M` factors uniquely through the reduction of `P`. -/
lemma existsUnique_complexMap_comp [res.Full] [res.Faithful] {P : CochainComplex 𝒜 ℤ}
    {M : CochainComplex 𝒜' ℤ} (g : P ⟶ (res.mapHomologicalComplex (.up ℤ)).obj M) :
    ∃! g' : (D.Φ.mapHomologicalComplex (.up ℤ)).obj P ⟶ M,
      D.complexMap P ≫ (res.mapHomologicalComplex (.up ℤ)).map g' = g :=
  ⟨D.descComplex g, D.complexMap_comp_descComplex g,
    fun _ hg' ↦ D.complexMap_ext (by rw [hg', complexMap_comp_descComplex])⟩

/-- Null-homotopies descend along the reduction: if `y : Φ(P) ⟶ M` becomes null-homotopic after
restriction and composition with the reduction of `P`, it is null-homotopic. -/
noncomputable def homotopyZero [res.Full] [res.Faithful] {P : CochainComplex 𝒜 ℤ}
    {M : CochainComplex 𝒜' ℤ} {y : (D.Φ.mapHomologicalComplex (.up ℤ)).obj P ⟶ M}
    (H : Homotopy (D.complexMap P ≫ (res.mapHomologicalComplex (.up ℤ)).map y) 0) :
    Homotopy y 0 where
  hom i j := D.desc (H.hom i j)
  zero i j hij := by
    refine D.hom_ext ?_
    have h₁ := D.r_app_comp_map_desc (H.hom i j)
    dsimp at h₁ ⊢
    rw [h₁, H.zero i j hij, Functor.map_zero, Limits.comp_zero]
  comm i := by
    refine D.hom_ext ?_
    have h := H.comm i
    have h₁ := D.r_app_comp_map_desc (H.hom (i + 1) i)
    have h₂ := D.r_app_comp_map_desc (H.hom i (i - 1))
    have hr := D.r.naturality (P.d i (i + 1))
    rw [dNext_eq _ (show (ComplexShape.up ℤ).Rel i (i + 1) by simp),
      prevD_eq _ (show (ComplexShape.up ℤ).Rel (i - 1) i by simp)] at h ⊢
    dsimp at h h₁ h₂ hr ⊢
    rw [add_zero] at h ⊢
    rw [Functor.map_add, Functor.map_comp, Functor.map_comp, Preadditive.comp_add,
      reassoc_of% h₂]
    erw [← reassoc_of% hr, h₁]
    exact h

omit [PreservesFiniteLimits res] [PreservesFiniteColimits res] in
/-- If `Q(P ⟶ res Φ(P) ⟶ res M)` vanishes for a K-flat complex `P`, then so does `Q(m)`. -/
lemma Q_map_eq_zero [res.Full] [res.Faithful] {P : CochainComplex 𝒜 ℤ}
    (hP : (HomologicalComplex.quasiIso 𝒜 (.up ℤ)).kFlat P) {M : CochainComplex 𝒜' ℤ}
    (m : (D.Φ.mapHomologicalComplex (.up ℤ)).obj P ⟶ M)
    (hm : DerivedCategory.Q.map (D.complexMap P ≫ (res.mapHomologicalComplex (.up ℤ)).map m) =
      0) :
    DerivedCategory.Q.map m = 0 := by
  obtain ⟨Z, u, hu, ⟨H⟩⟩ := DerivedCategory.exists_quasiIso_homotopy_zero_of_Q_map_eq_zero _ hm
  obtain ⟨Z', π, hπ, -, hZ'⟩ := CochainComplex.exists_quasiIso_flat_kFlat Z
  have := D.quasiIso_map (π ≫ u) hZ' hP
  have : IsIso (DerivedCategory.Q.map ((D.Φ.mapHomologicalComplex (.up ℤ)).map (π ≫ u))) := by
    rw [DerivedCategory.isIso_Q_map_iff_quasiIso]
    infer_instance
  have H' : Homotopy (D.complexMap Z' ≫ (res.mapHomologicalComplex (.up ℤ)).map
      ((D.Φ.mapHomologicalComplex (.up ℤ)).map (π ≫ u) ≫ m)) 0 :=
    (Homotopy.ofEq (by simp [← complexMap_naturality_assoc])).trans
      ((H.compLeft π).trans (.ofEq (by simp)))
  have := DerivedCategory.Q_map_eq_of_homotopy (h := D.homotopyZero H')
  rw [Functor.map_comp, Functor.map_zero] at this
  rwa [← cancel_epi (DerivedCategory.Q.map ((D.Φ.mapHomologicalComplex (.up ℤ)).map (π ≫ u))),
    Limits.comp_zero]

/-- The form of `bijective_comp_map` for an object of `D(𝒜')` given by a complex, with the
target identified with `Q(res M)`. -/
lemma bijective_comp_map_Q_obj [res.Full] [res.Faithful] (P : CochainComplex 𝒜 ℤ)
    (hP : (HomologicalComplex.quasiIso 𝒜 (.up ℤ)).kFlat P) (M : CochainComplex 𝒜' ℤ) :
    Function.Bijective fun g :
        DerivedCategory.Q.obj ((D.Φ.mapHomologicalComplex (.up ℤ)).obj P) ⟶
          DerivedCategory.Q.obj M ↦
      DerivedCategory.Q.map (D.complexMap P) ≫
        res.mapDerivedCategoryFactors.inv.app ((D.Φ.mapHomologicalComplex (.up ℤ)).obj P) ≫
        res.mapDerivedCategory.map g ≫ res.mapDerivedCategoryFactors.hom.app M := by
  refine ⟨fun g₁ g₂ hg ↦ ?_, fun φ ↦ ?_⟩
  · rw [← sub_eq_zero]
    obtain ⟨Y', w, t, ht, hwt⟩ := DerivedCategory.left_fac (g₁ - g₂)
    have h₀ : DerivedCategory.Q.map (D.complexMap P) ≫
        res.mapDerivedCategoryFactors.inv.app ((D.Φ.mapHomologicalComplex (.up ℤ)).obj P) ≫
        res.mapDerivedCategory.map (g₁ - g₂) ≫ res.mapDerivedCategoryFactors.hom.app M = 0 := by
      simp only [Functor.map_sub, Preadditive.sub_comp, Preadditive.comp_sub]
      exact sub_eq_zero.2 hg
    have hw : DerivedCategory.Q.map
        (D.complexMap P ≫ (res.mapHomologicalComplex (.up ℤ)).map w) = 0 := by
      rw [Functor.map_comp, ← mapDerivedCategoryFactors_inv_app_comp_map_comp_hom_app]
      rw [hwt] at h₀
      simpa using h₀ =≫ (res.mapDerivedCategoryFactors.inv.app M ≫
        res.mapDerivedCategory.map (DerivedCategory.Q.map t) ≫
        res.mapDerivedCategoryFactors.hom.app Y')
    rw [hwt, D.Q_map_eq_zero hP w hw, Limits.zero_comp]
  · obtain ⟨X, s, hs, g, rfl⟩ := DerivedCategory.right_fac φ
    obtain ⟨X', π, hπ, -, hX'⟩ := CochainComplex.exists_quasiIso_flat_kFlat X
    have : QuasiIso s := by rwa [← DerivedCategory.isIso_Q_map_iff_quasiIso]
    have := D.quasiIso_map (π ≫ s) hX' hP
    have : IsIso (DerivedCategory.Q.map ((D.Φ.mapHomologicalComplex (.up ℤ)).map (π ≫ s))) := by
      rw [DerivedCategory.isIso_Q_map_iff_quasiIso]
      infer_instance
    have : IsIso (DerivedCategory.Q.map (π ≫ s)) := by
      rw [DerivedCategory.isIso_Q_map_iff_quasiIso]
      infer_instance
    refine ⟨CategoryTheory.inv
      (DerivedCategory.Q.map ((D.Φ.mapHomologicalComplex (.up ℤ)).map (π ≫ s))) ≫
      DerivedCategory.Q.map (D.descComplex (π ≫ g)), ?_⟩
    dsimp only
    rw [← cancel_epi (DerivedCategory.Q.map (π ≫ s)), ← Functor.map_comp_assoc,
      complexMap_naturality, Functor.map_comp_assoc, mapDerivedCategoryFactors_inv_naturality_assoc,
      ← Functor.map_comp_assoc, IsIso.hom_inv_id_assoc,
      mapDerivedCategoryFactors_inv_app_comp_map_comp_hom_app, ← Functor.map_comp,
      complexMap_comp_descComplex]
    simp

/-- **The reduction of a K-flat complex is its derived base change**: for a K-flat complex
`P`, every morphism `Q P ⟶ res M` in `D(𝒜)` factors uniquely through the reduction
`Q P ⟶ res Q Φ(P)`. -/
theorem bijective_comp_map [res.Full] [res.Faithful] (P : CochainComplex 𝒜 ℤ)
    (hP : (HomologicalComplex.quasiIso 𝒜 (.up ℤ)).kFlat P) (M : DerivedCategory 𝒜') :
    Function.Bijective fun g :
        DerivedCategory.Q.obj ((D.Φ.mapHomologicalComplex (.up ℤ)).obj P) ⟶ M ↦
      (DerivedCategory.Q.map (D.complexMap P) ≫
        res.mapDerivedCategoryFactors.inv.app ((D.Φ.mapHomologicalComplex (.up ℤ)).obj P)) ≫
        res.mapDerivedCategory.map g := by
  let e := DerivedCategory.Q.objObjPreimageIso M
  convert ((res.mapDerivedCategory.mapIso e).homToEquiv.bijective.comp
    ((res.mapDerivedCategoryFactors.app _).symm.homToEquiv.bijective.comp
      (D.bijective_comp_map_Q_obj P hP _))).comp e.symm.homToEquiv.bijective using 1
  ext g
  simp [← Functor.map_comp]

end ReductionDatum

end CategoryTheory.Functor
