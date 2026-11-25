/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Descent
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex

/-! # Iterating an adjoint coefficient comparison through a flat extension

Source: Stacks Project, Tags 00HD and 05G3.
(blueprint: lem-pc-flat-iterated-scalar-extension-homology-square). -/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct ChangeOfRings
namespace ModuleCat

private theorem adjoint_homology
    (E D : Type u) [CommRing E] [CommRing D] (k : E →+* D) (hk : k.Flat)
    (Q : CochainComplex (ModuleCat.{u} E) ℤ)
    (T : CochainComplex (ModuleCat.{u} D) ℤ)
    (epsilon : ((extendScalars k).mapHomologicalComplex (.up ℤ)).obj Q ⟶ T)
    (φ : Q ⟶ ((restrictScalars k).mapHomologicalComplex (.up ℤ)).obj T)
    (htrans : ∀ j, φ.f j = (extendRestrictScalarsAdj k).homEquiv _ _ (epsilon.f j))
    (i : ℤ) :
    let F := extendScalars k
    let G := restrictScalars k
    letI := preservesFiniteLimits_extendScalars_of_flat hk
    (extendRestrictScalarsAdj k).homEquiv _ _
        (((Q.sc i).mapHomologyIso F).inv ≫ HomologicalComplex.homologyMap epsilon i) =
      HomologicalComplex.homologyMap φ i ≫ ((T.sc i).mapHomologyIso G).hom := by
  let F := extendScalars k
  let G := restrictScalars k
  let adj := extendRestrictScalarsAdj k
  have : PreservesFiniteLimits F := preservesFiniteLimits_extendScalars_of_flat hk
  let S := Q.sc i
  let U := T.sc i
  let ψ : S.map F ⟶ U := (HomologicalComplex.shortComplexFunctor _ _ i).map epsilon
  let τ : S ⟶ U.map G := (HomologicalComplex.shortComplexFunctor _ _ i).map φ
  let h := S.homologyData.left
  let k := U.homologyData.left
  let γ : ShortComplex.LeftHomologyMapData ψ (h.map F) k := default
  let δ : ShortComplex.LeftHomologyMapData τ h (k.map G) :=
    { φK := (adj.homEquiv _ _) γ.φK
      φH := (adj.homEquiv _ _) γ.φH
      commi := by
        change (adj.homEquiv _ _) γ.φK ≫ G.map k.i = h.i ≫ τ.τ₂
        rw [← adj.homEquiv_naturality_right]
        change _ = h.i ≫ φ.f i
        rw [htrans i]
        change _ = h.i ≫ (adj.homEquiv S.X₂ U.X₂) ψ.τ₂
        erw [← adj.homEquiv_naturality_left]
        exact congrArg (adj.homEquiv _ _) γ.commi
      commf' := by
        rw [ShortComplex.LeftHomologyData.map_f']
        change h.f' ≫ (adj.homEquiv _ _) γ.φK = τ.τ₁ ≫ G.map k.f'
        rw [← adj.homEquiv_naturality_left]
        change _ = φ.f ((ComplexShape.up ℤ).prev i) ≫ G.map k.f'
        rw [htrans, ← adj.homEquiv_naturality_right]
        change (adj.homEquiv S.X₁ k.K) (F.map h.f' ≫ γ.φK) =
          (adj.homEquiv S.X₁ k.K) (ψ.τ₁ ≫ k.f')
        apply congrArg (adj.homEquiv S.X₁ k.K)
        simpa only [ShortComplex.LeftHomologyData.map_f'] using γ.commf'
      commπ := by
        change h.π ≫ (adj.homEquiv _ _) γ.φH =
          (adj.homEquiv _ _) γ.φK ≫ G.map k.π
        rw [← adj.homEquiv_naturality_left, ← adj.homEquiv_naturality_right]
        exact congrArg (adj.homEquiv _ _) γ.commπ }
  have heq : ((adj.homEquiv _ _).symm
      (HomologicalComplex.homologyMap φ i ≫ (U.mapHomologyIso G).hom)) =
      F.map h.homologyIso.hom ≫ γ.φH ≫ k.homologyIso.inv := by
    apply (adj.homEquiv _ _).injective
    rw [Equiv.apply_symm_apply, adj.homEquiv_naturality_left,
      adj.homEquiv_naturality_right]
    change ShortComplex.homologyMap τ ≫ (U.mapHomologyIso G).hom = _
    rw [δ.homologyMap_eq, k.mapHomologyIso_eq G]
    simp [δ, Category.assoc]
    rfl
  change (adj.homEquiv _ _) ((S.mapHomologyIso F).inv ≫ ShortComplex.homologyMap ψ) =
    ShortComplex.homologyMap τ ≫ (U.mapHomologyIso G).hom
  apply (adj.homEquiv _ _).symm.injective
  rw [Equiv.symm_apply_apply]
  change _ = (adj.homEquiv _ _).symm
    (HomologicalComplex.homologyMap φ i ≫ (U.mapHomologyIso G).hom)
  rw [heq]
  change ((S.mapHomologyIso F).inv ≫ ShortComplex.homologyMap ψ) = _
  rw [h.mapHomologyIso_eq F, γ.homologyMap_eq]
  simp only [Iso.trans_inv, Functor.mapIso_inv, Iso.symm_inv, Category.assoc,
    Iso.inv_hom_id_assoc]

/-- The canonical comparisons to iterated and composite images of left homology
data agree. Their inclusions and projections are the same mapped morphisms. -/
private theorem iteratedHomologyData_comparison
    {C D E : Type*} [Category C] [Category D] [Category E]
    [HasZeroMorphisms C] [HasZeroMorphisms D] [HasZeroMorphisms E]
    (S : ShortComplex C) [S.HasHomology] (h : S.LeftHomologyData)
    (F : C ⥤ D) (G : D ⥤ E)
    [F.PreservesZeroMorphisms] [G.PreservesZeroMorphisms]
    [F.PreservesHomology] [G.PreservesHomology] [(F ⋙ G).PreservesHomology] :
    ((h.map F).map G).cyclesIso.hom = (h.map (F ⋙ G)).cyclesIso.hom ∧
      ((h.map F).map G).homologyIso.hom = (h.map (F ⋙ G)).homologyIso.hom := by
  have hc : ((h.map F).map G).cyclesIso.hom =
      (h.map (F ⋙ G)).cyclesIso.hom := by
    apply (cancel_mono (h.map (F ⋙ G)).i).1
    change _ ≫ ((h.map F).map G).i = _
    rw [ShortComplex.LeftHomologyData.cyclesIso_hom_comp_i,
      ShortComplex.LeftHomologyData.cyclesIso_hom_comp_i]
    rfl
  refine ⟨hc, ?_⟩
  apply (cancel_epi ((S.map F).map G).homologyπ).1
  rw [ShortComplex.LeftHomologyData.homologyπ_comp_homologyIso_hom,
    ShortComplex.LeftHomologyData.homologyπ_comp_homologyIso_hom, hc]
  rfl

/-- Mapping the cycles comparison twice agrees with mapping by the composite.
The proof compares both isomorphisms using the same left homology data; the
intermediate cycles isomorphism cancels after applying G. -/
private theorem mapCyclesIso_hom_comp
    {C D E : Type*} [Category C] [Category D] [Category E]
    [HasZeroMorphisms C] [HasZeroMorphisms D] [HasZeroMorphisms E]
    (S : ShortComplex C) [S.HasHomology]
    (F : C ⥤ D) (G : D ⥤ E)
    [F.PreservesZeroMorphisms] [G.PreservesZeroMorphisms]
    [F.PreservesHomology] [G.PreservesHomology] [(F ⋙ G).PreservesHomology] :
    ((S.map F).mapCyclesIso G).hom ≫ G.map (S.mapCyclesIso F).hom =
      (S.mapCyclesIso (F ⋙ G)).hom := by
  let h := S.leftHomologyData
  rw [(h.map F).mapCyclesIso_eq G, h.mapCyclesIso_eq F,
    h.mapCyclesIso_eq (F ⋙ G)]
  simp only [Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom, Functor.map_comp,
    Category.assoc]
  rw [← G.map_comp_assoc, Iso.inv_hom_id, G.map_id, Category.id_comp,
    (iteratedHomologyData_comparison S h F G).1]
  rfl

/-- Mapping the homology comparison twice agrees with mapping by the composite.
As for cycles, choose the original left homology data and its two successive
images. The comparison with the intermediate canonical homology cancels. -/
private theorem mapHomologyIso_hom_comp
    {C D E : Type*} [Category C] [Category D] [Category E]
    [HasZeroMorphisms C] [HasZeroMorphisms D] [HasZeroMorphisms E]
    (S : ShortComplex C) [S.HasHomology]
    (F : C ⥤ D) (G : D ⥤ E)
    [F.PreservesZeroMorphisms] [G.PreservesZeroMorphisms]
    [F.PreservesHomology] [G.PreservesHomology] [(F ⋙ G).PreservesHomology] :
    ((S.map F).mapHomologyIso G).hom ≫ G.map (S.mapHomologyIso F).hom =
      (S.mapHomologyIso (F ⋙ G)).hom := by
  let h := S.homologyData.left
  rw [(h.map F).mapHomologyIso_eq G, h.mapHomologyIso_eq F,
    h.mapHomologyIso_eq (F ⋙ G)]
  simp only [Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom, Functor.map_comp,
    Category.assoc]
  rw [← G.map_comp_assoc, Iso.inv_hom_id, G.map_id, Category.id_comp,
    (iteratedHomologyData_comparison S h F G).2]
  rfl

private theorem forgetAdjunct
    (E D : Type u) [CommRing E] [CommRing D] (f : E →+* D)
    (S : ModuleCat.{u} E) (X : CochainComplex (ModuleCat.{u} E) ℤ)
    (Y : CochainComplex (ModuleCat.{u} D) ℤ) (i : ℤ)
    (a : S ⟶ X.homology i)
    (v : X ⟶ ((restrictScalars f).mapHomologicalComplex (.up ℤ)).obj Y)
    (aD : (extendScalars f).obj S ⟶ Y.homology i)
    (ha : (extendRestrictScalarsAdj f).unit.app S ≫ (restrictScalars f).map aD =
      a ≫ HomologicalComplex.homologyMap v i ≫
        ((Y.sc i).mapHomologyIso (restrictScalars f)).hom) :
    let UE := forget₂ (ModuleCat.{u} E) AddCommGrpCat.{u}
    let UD := forget₂ (ModuleCat.{u} D) AddCommGrpCat.{u}
    UE.map ((extendRestrictScalarsAdj f).unit.app S) ≫ UD.map aD ≫
        ((Y.sc i).mapHomologyIso UD).inv =
      UE.map a ≫ ((X.sc i).mapHomologyIso UE).inv ≫ HomologicalComplex.homologyMap
        ((UE.mapHomologicalComplex (.up ℤ)).map v) i := by
  let UE := forget₂ (ModuleCat.{u} E) AddCommGrpCat.{u}
  let UD := forget₂ (ModuleCat.{u} D) AddCommGrpCat.{u}
  let sx := (X.sc i).mapHomologyIso UE
  let sy := (Y.sc i).mapHomologyIso UD
  have hx : UE.map (HomologicalComplex.homologyMap v i) ≫
      UE.map ((Y.sc i).mapHomologyIso (restrictScalars f)).hom =
      sx.inv ≫ HomologicalComplex.homologyMap
        ((UE.mapHomologicalComplex (.up ℤ)).map v) i ≫ sy.hom := by
    apply (cancel_epi sx.hom).1
    simp only [Iso.hom_inv_id_assoc]
    let tx := ((((restrictScalars f).mapHomologicalComplex (.up ℤ)).obj
      Y).sc i).mapHomologyIso UE
    have hn : HomologicalComplex.homologyMap
        ((UE.mapHomologicalComplex (.up ℤ)).map v) i ≫
          tx.hom = sx.hom ≫ UE.map (HomologicalComplex.homologyMap v i) := by
      exact ShortComplex.mapHomologyIso_hom_naturality
        ((HomologicalComplex.shortComplexFunctor _ (.up ℤ) i).map v) UE
    have hc : tx.hom ≫
        UE.map ((Y.sc i).mapHomologyIso (restrictScalars f)).hom = sy.hom := by
      exact mapHomologyIso_hom_comp (Y.sc i) (restrictScalars f) UE
    rw [← Category.assoc, ← hn, Category.assoc, hc]
  have hax := congrArg UE.map ha
  dsimp only [UE] at hax
  simp only [Functor.map_comp, forget₂_map_restrictScalars] at hax
  rw [hx] at hax
  have ht := congrArg (fun z ↦ z ≫ sy.inv) hax
  simpa only [Category.assoc, Iso.hom_inv_id, Category.comp_id] using ht

/-- The coefficient adjunction and exact homology comparison commute with iteration.
Source: Stacks Project, Tag 00HD (exact tensor by a flat module) and Tag 05G3
(extension/restriction adjunction).
(blueprint: lem-pc-flat-iterated-scalar-extension-homology-square).

Proof: transpose the desired equality twice, first through extension from E to D
and then through extension from T to E. On 1 tensor (1 tensor x), the hypothesis
on e changes the right hand side to aD(1 tensor s(x)). The formulas ha and hb
express both sides in terms of a and b and homology of vE and vD. Exactness of
extension along k identifies cohomology of extension with extension of cohomology;
its inverse in the conclusion is the map induced on cycles and boundaries.
Naturality of this comparison with the adjunction unit identifies the left hand
side with homology of the coefficient chain map x -> tau(1 tensor vE(x)).
Tensor induction using the generator equations for vE, vD and tau identifies that
chain map with vD. Substitute s.hom followed by b equals a. The two restriction
homology isomorphisms combine by naturality of homology of the composite exact
restriction functor. Thus the two transposes agree, and adjunction injectivity
proves the equation. Only k needs to be flat: the other homology maps are taken
after coefficient extension, without commuting nonexact tensor with homology.
For zero complexes and zero rings the same unit identities hold; for k the
identity this is ordinary naturality. -/
theorem flatIteratedScalarExtension_homology_square
    (A T E D : Type u) [CommRing A] [CommRing T] [CommRing E] [CommRing D]
    (f : A →+* T) (c : T →+* E) (d : T →+* D) (k : E →+* D)
    (hk : k.Flat) (hcomp : k.comp c = d)
    (Q : CochainComplex (ModuleCat.{u} A) ℤ) (i : ℤ) :
    let X := ((extendScalars f).mapHomologicalComplex (.up ℤ)).obj Q
    let XE := ((extendScalars (c.comp f)).mapHomologicalComplex (.up ℤ)).obj Q
    let XD := ((extendScalars (d.comp f)).mapHomologicalComplex (.up ℤ)).obj Q
    let F := extendScalars k
    letI := preservesFiniteLimits_extendScalars_of_flat hk
    ∀ (S N : ModuleCat.{u} T) (s : S ≅ N)
      (a : S ⟶ X.homology i) (b : N ⟶ X.homology i),
      s.hom ≫ b = a →
      ∀ (vE : X ⟶ ((restrictScalars c).mapHomologicalComplex (.up ℤ)).obj XE)
        (vD : X ⟶ ((restrictScalars d).mapHomologicalComplex (.up ℤ)).obj XD),
      (∀ (j : ℤ) (t : T) (q : Q.X j),
        vE.f j (t ⊗ₜ[A, f] q) = c t ⊗ₜ[A, c.comp f] q) →
      (∀ (j : ℤ) (t : T) (q : Q.X j),
        vD.f j (t ⊗ₜ[A, f] q) = d t ⊗ₜ[A, d.comp f] q) →
      ∀ (aE : (extendScalars c).obj S ⟶ XE.homology i)
        (aD : (extendScalars d).obj N ⟶ XD.homology i),
      (extendRestrictScalarsAdj c).unit.app S ≫ (restrictScalars c).map aE =
        a ≫ HomologicalComplex.homologyMap vE i ≫
          ((XE.sc i).mapHomologyIso (restrictScalars c)).hom →
      (extendRestrictScalarsAdj d).unit.app N ≫ (restrictScalars d).map aD =
        b ≫ HomologicalComplex.homologyMap vD i ≫
          ((XD.sc i).mapHomologyIso (restrictScalars d)).hom →
      ∀ (e : F.obj ((extendScalars c).obj S) ≅ (extendScalars d).obj N),
      (∀ x : S, e.hom ((1 : D) ⊗ₜ[E, k] ((1 : E) ⊗ₜ[T, c] x)) =
        (1 : D) ⊗ₜ[T, d] (s.hom x)) →
      ∀ tau : (F.mapHomologicalComplex (.up ℤ)).obj XE ≅ XD,
      (∀ (j : ℤ) (x : Q.X j),
        tau.hom.f j ((1 : D) ⊗ₜ[E, k] ((1 : E) ⊗ₜ[A, c.comp f] x)) =
          (1 : D) ⊗ₜ[A, d.comp f] x) →
      F.map aE ≫ ((XE.sc i).mapHomologyIso F).inv ≫
        HomologicalComplex.homologyMap tau.hom i = e.hom ≫ aD := by
  dsimp only
  intro S N s a b hs vE vD hvE hvD aE aD ha hb e he tau htau
  let X := ((extendScalars f).mapHomologicalComplex (.up ℤ)).obj Q
  let XE := ((extendScalars (c.comp f)).mapHomologicalComplex (.up ℤ)).obj Q
  let XD := ((extendScalars (d.comp f)).mapHomologicalComplex (.up ℤ)).obj Q
  let F := extendScalars k
  let G := restrictScalars k
  let adj := extendRestrictScalarsAdj k
  have : PreservesFiniteLimits F := preservesFiniteLimits_extendScalars_of_flat hk
  let UT := forget₂ (ModuleCat.{u} T) AddCommGrpCat.{u}
  let UE := forget₂ (ModuleCat.{u} E) AddCommGrpCat.{u}
  let UD := forget₂ (ModuleCat.{u} D) AddCommGrpCat.{u}
  let SX := (X.sc i).mapHomologyIso UT
  let SE := (XE.sc i).mapHomologyIso UE
  let SD := (XD.sc i).mapHomologyIso UD
  let eta := (adj.unit.mapHomologicalComplex (.up ℤ)).app XE
  let v : XE ⟶ (G.mapHomologicalComplex (.up ℤ)).obj XD :=
    eta ≫ (G.mapHomologicalComplex (.up ℤ)).map tau.hom
  have hv (j : ℤ) : v.f j = (adj.homEquiv _ _) (tau.hom.f j) := by
    rfl
  let aK : F.obj (XE.homology i) ⟶ XD.homology i :=
    ((XE.sc i).mapHomologyIso F).inv ≫ HomologicalComplex.homologyMap tau.hom i
  have haK : adj.unit.app (XE.homology i) ≫ G.map aK =
      𝟙 _ ≫ HomologicalComplex.homologyMap v i ≫
        ((XD.sc i).mapHomologyIso G).hom := by
    simpa only [Category.id_comp, Adjunction.homEquiv_unit, aK, F, G, adj,
      HomologicalComplex.homology] using
      adjoint_homology E D k hk XE XD tau.hom v hv i
  have hA := forgetAdjunct T E c S X XE i a vE aE ha
  have hB := forgetAdjunct T D d N X XD i b vD aD hb
  have hK := forgetAdjunct E D k (XE.homology i) XE XD i (𝟙 _) v aK haK
  change UE.map (adj.unit.app (XE.homology i)) ≫ UD.map aK ≫ SD.inv =
    UE.map (𝟙 _) ≫ SE.inv ≫ HomologicalComplex.homologyMap
      ((UE.mapHomologicalComplex (.up ℤ)).map v) i at hK
  erw [UE.map_id, Category.id_comp] at hK
  have hvcomp : (UT.mapHomologicalComplex (.up ℤ)).map vE ≫
      (UE.mapHomologicalComplex (.up ℤ)).map v =
        (UT.mapHomologicalComplex (.up ℤ)).map vD := by
    apply HomologicalComplex.Hom.ext
    funext j
    apply AddCommGrpCat.hom_ext
    ext z
    induction z using TensorProduct.inductionOn with
    | tmul t x =>
      change tau.hom.f j ((1 : D) ⊗ₜ[E, k] (vE.f j (t ⊗ₜ[A, f] x))) =
        vD.f j (t ⊗ₜ[A, f] x)
      rw [hvE, hvD]
      have hin : c t ⊗ₜ[A, c.comp f] x =
          c t • ((1 : E) ⊗ₜ[A, c.comp f] x) := by
        rw [ExtendScalars.smul_tmul, mul_one]
      rw [hin, TensorProduct.tmul_smul]
      change tau.hom.f j ((k (c t)) •
        ((1 : D) ⊗ₜ[E, k] ((1 : E) ⊗ₜ[A, c.comp f] x))) = _
      rw [map_smul, htau, ExtendScalars.smul_tmul, mul_one]
      congr 1
      exact DFunLike.congr_fun hcomp t
    | add z z' hz hz' => simp only [map_add] at hz hz' ⊢; rw [hz, hz']
  let uC := UT.map ((extendRestrictScalarsAdj c).unit.app S)
  let uK := UE.map (adj.unit.app ((extendScalars c).obj S))
  let uD := UT.map ((extendRestrictScalarsAdj d).unit.app N)
  have heq : uC ≫ uK ≫ UD.map e.hom = UT.map s.hom ≫ uD := by
    apply AddCommGrpCat.hom_ext
    ext x
    exact he x
  have hn := congrArg UE.map (adj.unit.naturality aE)
  dsimp only [UE] at hn
  simp only [Functor.id_map, Functor.comp_map, Functor.map_comp,
    forget₂_map_restrictScalars] at hn
  have hvH := congrArg (fun z ↦ HomologicalComplex.homologyMap z i) hvcomp
  simp only [HomologicalComplex.homologyMap_comp] at hvH
  have hs' := congrArg UT.map hs
  simp only [Functor.map_comp] at hs'
  have hw : uC ≫ uK ≫ UD.map (F.map aE) ≫ UD.map aK ≫ SD.inv =
      uC ≫ uK ≫ UD.map e.hom ≫ UD.map aD ≫ SD.inv := by
    calc
      _ = uC ≫ UE.map aE ≫ UE.map (adj.unit.app (XE.homology i)) ≫ UD.map aK ≫ SD.inv := by
        simpa only [Category.assoc, uK, UE, UD, F, XE,
          HomologicalComplex.homology] using
          congrArg (fun z ↦ uC ≫ z ≫ UD.map aK ≫ SD.inv) hn.symm
      _ = uC ≫ UE.map aE ≫ SE.inv ≫ HomologicalComplex.homologyMap
          ((UE.mapHomologicalComplex (.up ℤ)).map v) i := by
        simpa only [Category.assoc, XE, HomologicalComplex.homology] using
          congrArg (fun z ↦ uC ≫ UE.map aE ≫ z) hK
      _ = UT.map a ≫ SX.inv ≫ HomologicalComplex.homologyMap
          ((UT.mapHomologicalComplex (.up ℤ)).map vE) i ≫
            HomologicalComplex.homologyMap ((UE.mapHomologicalComplex (.up ℤ)).map v) i := by
        simpa only [Category.assoc] using congrArg (fun z ↦ z ≫
          HomologicalComplex.homologyMap ((UE.mapHomologicalComplex (.up ℤ)).map v) i) hA
      _ = UT.map a ≫ SX.inv ≫ HomologicalComplex.homologyMap
          ((UT.mapHomologicalComplex (.up ℤ)).map vD) i := by rw [hvH]
      _ = UT.map s.hom ≫ UT.map b ≫ SX.inv ≫ HomologicalComplex.homologyMap
          ((UT.mapHomologicalComplex (.up ℤ)).map vD) i := by rw [← hs']; simp [Category.assoc]
      _ = UT.map s.hom ≫ uD ≫ UD.map aD ≫ SD.inv := by
        simpa only [Category.assoc] using congrArg (fun z ↦ UT.map s.hom ≫ z) hB.symm
      _ = _ := by
        simpa only [Category.assoc] using
          congrArg (fun z ↦ z ≫ UD.map aD ≫ SD.inv) heq.symm
  have hw' : uC ≫ uK ≫ UD.map (F.map aE) ≫ UD.map aK =
      uC ≫ uK ≫ UD.map e.hom ≫ UD.map aD := by
    apply (cancel_mono SD.inv).1
    simpa only [Category.assoc] using hw
  apply (adj.homEquiv _ _).injective
  apply ExtendScalars.hom_ext
  intro x
  exact congrArg (fun z ↦ z x) hw'


end ModuleCat
