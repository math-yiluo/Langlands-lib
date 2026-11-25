/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRingsExact
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex

/-! # Extending an ordinary homology comparison square

Source: Stacks Project, Tag 05G3, scalar extension and its adjunction;
Tag 06Y6, passage from ordinary tensor comparison to coefficient extension.
(blueprint: lem-pc-semilinear-scalar-extension-homology-square).
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory
open scoped TensorProduct ChangeOfRings
namespace ModuleCat

private theorem exists_extensionIso
    {S₀ S D₀ D : Type u}
    [CommRing S₀] [CommRing S] [CommRing D₀] [CommRing D]
    (f₀ : S₀ →+* D₀) (f : S →+* D)
    (eS : S₀ ≃+* S) (eD : D₀ ≃+* D)
    (hf : eD.toRingHom.comp f₀ = f.comp eS.toRingHom)
    (P₀ : ModuleCat.{u} S₀) (P : ModuleCat.{u} S)
    (k : P₀ ≅ (restrictScalars.{u} eS.toRingHom).obj P) :
    ∃ l : (extendScalars f₀).obj P₀ ≅
        (restrictScalars.{u} eD.toRingHom).obj ((extendScalars f).obj P),
      ∀ (d : D₀) (p : P₀), l.hom (d ⊗ₜ[S₀, f₀] p) =
        eD d ⊗ₜ[S, f] (show P from k.hom p) := by
  let : Module S₀ D₀ := Module.compHom D₀ f₀
  let : Module S D := Module.compHom D f
  have : RingHomInvPair eS.toRingHom eS.symm.toRingHom :=
    RingHomInvPair.of_ringEquiv eS
  have : RingHomInvPair eS.symm.toRingHom eS.toRingHom :=
    RingHomInvPair.of_ringEquiv_symm eS
  let c : LinearEquiv eS.toRingHom (σ' := eS.symm.toRingHom) D₀ D :=
    { __ := eD.toAddEquiv
      map_smul' := by
        intro r d
        change eD (f₀ r * d) = f (eS r) * eD d
        rw [map_mul]
        exact congrArg (fun z ↦ z * eD d) (RingHom.congr_fun hf r) }
  let h : LinearEquiv eS.toRingHom (σ' := eS.symm.toRingHom) P₀ P :=
    { __ := k.toLinearEquiv.toAddEquiv
      map_smul' := fun r p ↦ (k.hom.hom.map_smul r p) }
  let v := TensorProduct.congr c h
  let l : (extendScalars f₀).obj P₀ ≃ₗ[D₀]
      (restrictScalars.{u} eD.toRingHom).obj ((extendScalars f).obj P) :=
    { __ := v.toAddEquiv
      map_smul' := by
        intro d z
        change v (d • z) = eD d • v z
        induction z using TensorProduct.inductionOn with
        | tmul d' p =>
          change v ((d * (show D₀ from d')) ⊗ₜ[S₀, f₀] p) =
            eD d • v (d' ⊗ₜ[S₀, f₀] p)
          rw [TensorProduct.congr_tmul, TensorProduct.congr_tmul]
          change eD (d * (show D₀ from d')) ⊗ₜ[S, f] (show P from k.hom p) = _
          rw [map_mul]
          rfl
        | add z w hz hw =>
          change v (d • (z + w)) = eD d • v (z + w)
          rw [smul_add, map_add, map_add, hz, hw, smul_add] }
  exact ⟨l.toModuleIso, fun d p ↦ TensorProduct.congr_tmul c h d p⟩

private theorem forgetHomologyIso_comp
    {S T : Type u} [CommRing S] [CommRing T] (f : S →+* T)
    (K : ShortComplex (ModuleCat.{u} T)) :
    let G := restrictScalars.{u} f
    let F := forget₂ (ModuleCat.{u} S) AddCommGrpCat.{u}
    let F' := forget₂ (ModuleCat.{u} T) AddCommGrpCat.{u}
    ((K.map G).mapHomologyIso F).hom ≫
        F.map (K.mapHomologyIso G).hom =
      (K.mapHomologyIso F').hom := by
  dsimp only
  let h := K.homologyData.left
  rw [(h.map (restrictScalars.{u} f)).mapHomologyIso_eq,
    h.mapHomologyIso_eq, h.mapHomologyIso_eq]
  simp only [Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom, Functor.map_comp,
    Category.assoc]
  simp only [← Functor.map_comp, Iso.inv_hom_id_assoc]
  let γ : ShortComplex.LeftHomologyMapData
      (𝟙 (K.map (forget₂ (ModuleCat.{u} T) AddCommGrpCat.{u})))
      ((h.map (restrictScalars.{u} f)).map
        (forget₂ (ModuleCat.{u} S) AddCommGrpCat.{u}))
      (h.map (forget₂ (ModuleCat.{u} T) AddCommGrpCat.{u})) :=
    { φK := 𝟙 _
      φH := 𝟙 _
      commi := by ext x; rfl
      commπ := by ext x; rfl }
  have hh := γ.homologyMap_comm
  simp only [γ, ShortComplex.homologyMap_id, Category.id_comp, Category.comp_id] at hh
  rw [← hh]
  rfl

private theorem forgetHomologyMap
    {S T : Type u} [CommRing S] [CommRing T] (f : S →+* T)
    (K : CochainComplex (ModuleCat.{u} S) ℤ)
    (L : CochainComplex (ModuleCat.{u} T) ℤ)
    (φ : K ⟶ ((restrictScalars.{u} f).mapHomologicalComplex (.up ℤ)).obj L)
    (i : ℤ) :
    let F := forget₂ (ModuleCat.{u} S) AddCommGrpCat.{u}
    let F' := forget₂ (ModuleCat.{u} T) AddCommGrpCat.{u}
    F.map (HomologicalComplex.homologyMap φ i) ≫
        F.map ((L.sc i).mapHomologyIso (restrictScalars.{u} f)).hom =
      ((K.sc i).mapHomologyIso F).inv ≫
        HomologicalComplex.homologyMap ((F.mapHomologicalComplex (.up ℤ)).map φ) i ≫
        ((L.sc i).mapHomologyIso F').hom := by
  dsimp only
  let F := forget₂ (ModuleCat.{u} S) AddCommGrpCat.{u}
  let F' := forget₂ (ModuleCat.{u} T) AddCommGrpCat.{u}
  let G := restrictScalars.{u} f
  have hn := ShortComplex.mapHomologyIso_hom_naturality
    ((HomologicalComplex.shortComplexFunctor _ _ i).map φ) F
  change HomologicalComplex.homologyMap ((F.mapHomologicalComplex (.up ℤ)).map φ) i ≫
      (((L.sc i).map G).mapHomologyIso F).hom =
    ((K.sc i).mapHomologyIso F).hom ≫
      F.map (HomologicalComplex.homologyMap φ i) at hn
  rw [← forgetHomologyIso_comp f (L.sc i)]
  rw [reassoc_of% hn]
  simp only [F, Iso.inv_hom_id_assoc]

/-- Scalar extension transports a homology square whenever its adjoint formulas
and the intervening chain square commute. No derived category is involved.

Proof: construct the extension isomorphism on pure tensors by
 d tensor p ↦ eD(d) tensor k(p). Compatibility of the structural maps and
semilinearity of k prove balance; the inverse uses eD inverse and k inverse.
Tensor induction proves both inverse identities and eD-semilinearity.
Forget this isomorphism to obtain l. Transpose the desired square through the
extension/restriction adjunction. The two specified equations for b0 and b
replace their transposes by a0 and a followed by homology of delta0 and delta.
Apply the ordinary square ha and the homology of the given additive chain
square hdelta. Exact restriction and forgetting commute with homology; their
comparison isomorphisms compose by comparing the twice-mapped left homology
data with the directly mapped data, using identity maps on cycles and homology.
Homology naturality then cancels these isomorphisms. Equality on unit tensors
proves equality of the adjoints, and linearity proves it on all pure tensors.
This proves the square. For identity coefficient isomorphisms this is ordinary
naturality of adjunction. For zero modules or complexes it is the zero square.
Nonflat structural maps are allowed: only restriction and forgetting, not
extension, must preserve homology. Neither a nor b must be invertible.
Source: Stacks Project, Tag 05G3, extension of scalars; Tag 06Y6,
lemma-derived-base-change, ordinary comparison followed by coefficient extension.
(blueprint: lem-pc-semilinear-scalar-extension-homology-square). -/
theorem exists_scalarExtension_homology_square
    {S₀ S D₀ D : Type u}
    [CommRing S₀] [CommRing S] [CommRing D₀] [CommRing D]
    (f₀ : S₀ →+* D₀) (f : S →+* D)
    (eS : S₀ ≃+* S) (eD : D₀ ≃+* D)
    (hf : eD.toRingHom.comp f₀ = f.comp eS.toRingHom)
    (P₀ : ModuleCat.{u} S₀) (P : ModuleCat.{u} S)
    (K₀ : CochainComplex (ModuleCat.{u} S₀) ℤ)
    (K : CochainComplex (ModuleCat.{u} S) ℤ)
    (X₀ : CochainComplex (ModuleCat.{u} D₀) ℤ)
    (X : CochainComplex (ModuleCat.{u} D) ℤ)
    (s : K₀ ≅ ((restrictScalars.{u} eS.toRingHom).mapHomologicalComplex (.up ℤ)).obj K)
    (t : X₀ ≅ ((restrictScalars.{u} eD.toRingHom).mapHomologicalComplex (.up ℤ)).obj X)
    (k : P₀ ≅ (restrictScalars.{u} eS.toRingHom).obj P)
    (δ₀ : K₀ ⟶ ((restrictScalars.{u} f₀).mapHomologicalComplex (.up ℤ)).obj X₀)
    (δ : K ⟶ ((restrictScalars.{u} f).mapHomologicalComplex (.up ℤ)).obj X)
    (hδ :
      ((forget₂ (ModuleCat.{u} S₀) AddCommGrpCat.{u}).mapHomologicalComplex (.up ℤ)).map δ₀ ≫
        ((forget₂ (ModuleCat.{u} D₀) AddCommGrpCat.{u}).mapHomologicalComplex
          (.up ℤ)).map t.hom =
      ((forget₂ (ModuleCat.{u} S₀) AddCommGrpCat.{u}).mapHomologicalComplex
          (.up ℤ)).map s.hom ≫
        ((forget₂ (ModuleCat.{u} S) AddCommGrpCat.{u}).mapHomologicalComplex (.up ℤ)).map δ)
    (i : ℤ) (a₀ : P₀ ⟶ K₀.homology i) (a : P ⟶ K.homology i)
    (ha : k.hom ≫ (restrictScalars.{u} eS.toRingHom).map a ≫
        ((K.sc i).mapHomologyIso (restrictScalars.{u} eS.toRingHom)).inv =
      a₀ ≫ HomologicalComplex.homologyMap s.hom i)
    (b₀ : (extendScalars f₀).obj P₀ ⟶ X₀.homology i)
    (b : (extendScalars f).obj P ⟶ X.homology i)
    (hb₀ : (extendRestrictScalarsAdj f₀).unit.app P₀ ≫
        (restrictScalars.{u} f₀).map b₀ =
      a₀ ≫ HomologicalComplex.homologyMap δ₀ i ≫
        ((X₀.sc i).mapHomologyIso (restrictScalars.{u} f₀)).hom)
    (hb : (extendRestrictScalarsAdj f).unit.app P ≫
        (restrictScalars.{u} f).map b =
      a ≫ HomologicalComplex.homologyMap δ i ≫
        ((X.sc i).mapHomologyIso (restrictScalars.{u} f)).hom) :
    let F₀ := forget₂ (ModuleCat.{u} D₀) AddCommGrpCat.{u}
    let F := forget₂ (ModuleCat.{u} D) AddCommGrpCat.{u}
    ∃ l : F₀.obj ((extendScalars f₀).obj P₀) ≅ F.obj ((extendScalars f).obj P),
      l.hom ≫ F.map b ≫ F₀.map ((X.sc i).mapHomologyIso
          (restrictScalars.{u} eD.toRingHom)).inv =
        F₀.map b₀ ≫ F₀.map (HomologicalComplex.homologyMap t.hom i) := by
  let F₀ := forget₂ (ModuleCat.{u} D₀) AddCommGrpCat.{u}
  let F := forget₂ (ModuleCat.{u} D) AddCommGrpCat.{u}
  let E₀ := forget₂ (ModuleCat.{u} S₀) AddCommGrpCat.{u}
  let E := forget₂ (ModuleCat.{u} S) AddCommGrpCat.{u}
  let H := HomologicalComplex.homologyFunctor AddCommGrpCat.{u} (.up ℤ) i
  let cK₀ := (K₀.sc i).mapHomologyIso E₀
  let cK := (K.sc i).mapHomologyIso E
  let cX₀ := (X₀.sc i).mapHomologyIso F₀
  let cX := (X.sc i).mapHomologyIso F
  let d₀ := (E₀.mapHomologicalComplex (.up ℤ)).map δ₀
  let d := (E.mapHomologicalComplex (.up ℤ)).map δ
  let v := (E₀.mapHomologicalComplex (.up ℤ)).map s.hom
  let z := (F₀.mapHomologicalComplex (.up ℤ)).map t.hom
  let u₀ := (extendRestrictScalarsAdj f₀).unit.app P₀
  let u := (extendRestrictScalarsAdj f).unit.app P
  have hB₀ : E₀.map u₀ ≫ F₀.map b₀ =
      E₀.map a₀ ≫ cK₀.inv ≫ H.map d₀ ≫ cX₀.hom := by
    have hh := congrArg E₀.map hb₀
    simp only [Functor.map_comp] at hh
    change E₀.map u₀ ≫ F₀.map b₀ = E₀.map a₀ ≫
      E₀.map (HomologicalComplex.homologyMap δ₀ i) ≫
      E₀.map ((X₀.sc i).mapHomologyIso (restrictScalars.{u} f₀)).hom at hh
    exact hh.trans (congrArg (fun m ↦ E₀.map a₀ ≫ m)
      (forgetHomologyMap f₀ K₀ X₀ δ₀ i))
  have hB : E.map u ≫ F.map b = E.map a ≫ cK.inv ≫ H.map d ≫ cX.hom := by
    have hh := congrArg E.map hb
    simp only [Functor.map_comp] at hh
    change E.map u ≫ F.map b = E.map a ≫
      E.map (HomologicalComplex.homologyMap δ i) ≫
      E.map ((X.sc i).mapHomologyIso (restrictScalars.{u} f)).hom at hh
    exact hh.trans (congrArg (fun m ↦ E.map a ≫ m) (forgetHomologyMap f K X δ i))
  have hA : E₀.map k.hom ≫ E.map a =
      E₀.map a₀ ≫ cK₀.inv ≫ H.map v ≫ cK.hom := by
    have hh := congrArg
      (fun m ↦ E₀.map (m ≫ ((K.sc i).mapHomologyIso
        (restrictScalars.{u} eS.toRingHom)).hom)) ha
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id, Functor.map_comp] at hh
    change E₀.map k.hom ≫ E.map a = E₀.map a₀ ≫
      E₀.map (HomologicalComplex.homologyMap s.hom i) ≫
      E₀.map ((K.sc i).mapHomologyIso (restrictScalars.{u} eS.toRingHom)).hom at hh
    exact hh.trans (congrArg (fun m ↦ E₀.map a₀ ≫ m)
      (forgetHomologyMap eS.toRingHom K₀ K s.hom i))
  have hT := forgetHomologyMap eD.toRingHom X₀ X t.hom i
  change F₀.map (HomologicalComplex.homologyMap t.hom i) ≫
      F₀.map ((X.sc i).mapHomologyIso (restrictScalars.{u} eD.toRingHom)).hom =
    cX₀.inv ≫ H.map z ≫ cX.hom at hT
  have hchain : H.map d₀ ≫ H.map z = H.map v ≫ H.map d := by
    rw [← H.map_comp, ← H.map_comp, hδ]
  have hunit : E₀.map u₀ ≫ F₀.map b₀ ≫
        F₀.map (HomologicalComplex.homologyMap t.hom i) ≫
        F₀.map ((X.sc i).mapHomologyIso (restrictScalars.{u} eD.toRingHom)).hom =
      E₀.map k.hom ≫ E.map u ≫ F.map b := by
    simp only [← Category.assoc]
    rw [hB₀]
    simp only [Category.assoc]
    rw [hT]
    simp only [Iso.hom_inv_id_assoc]
    rw [hB, reassoc_of% hA]
    simp only [Iso.hom_inv_id_assoc]
    rw [reassoc_of% hchain]
  obtain ⟨l, hl⟩ := exists_extensionIso f₀ f eS eD hf P₀ P k
  have hsquare : l.hom ≫ (restrictScalars.{u} eD.toRingHom).map b =
      b₀ ≫ HomologicalComplex.homologyMap t.hom i ≫
        ((X.sc i).mapHomologyIso (restrictScalars.{u} eD.toRingHom)).hom := by
    apply ExtendScalars.hom_ext
    intro p
    have hh := ConcreteCategory.congr_hom hunit p
    change ((X.sc i).mapHomologyIso (restrictScalars.{u} eD.toRingHom)).hom
        ((HomologicalComplex.homologyMap t.hom i) (b₀ ((1 : D₀) ⊗ₜ[S₀, f₀] p))) =
      b ((1 : D) ⊗ₜ[S, f] (show P from k.hom p)) at hh
    change b (l.hom ((1 : D₀) ⊗ₜ[S₀, f₀] p)) =
      ((X.sc i).mapHomologyIso (restrictScalars.{u} eD.toRingHom)).hom
        ((HomologicalComplex.homologyMap t.hom i) (b₀ ((1 : D₀) ⊗ₜ[S₀, f₀] p)))
    rw [hl, map_one]
    exact hh.symm
  refine ⟨F₀.mapIso l, ?_⟩
  have hh := congrArg
    (fun m ↦ F₀.map (m ≫ ((X.sc i).mapHomologyIso
      (restrictScalars.{u} eD.toRingHom)).inv)) hsquare
  change F₀.map l.hom ≫ F₀.map ((restrictScalars.{u} eD.toRingHom).map b) ≫
      F₀.map ((X.sc i).mapHomologyIso (restrictScalars.{u} eD.toRingHom)).inv =
    F₀.map b₀ ≫ F₀.map (HomologicalComplex.homologyMap t.hom i)
  simpa only [Functor.map_comp, Category.assoc, Iso.hom_inv_id, Category.comp_id] using hh

end ModuleCat
