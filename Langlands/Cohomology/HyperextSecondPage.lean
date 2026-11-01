import Langlands.Cohomology.HyperextSpectralSequence
import Mathlib.Algebra.Category.Grp.Zero
import Mathlib.Algebra.Homology.DerivedCategory.Ext.Basic
import Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful
import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
import Mathlib.Algebra.Homology.DerivedCategory.TStructure

/-!
# The second page of the hyperext spectral sequence in a derived category

For the standard t-structure `TStructure.t` on the derived category of an abelian category `C`,
an object `K` of the derived category and an object `W` of `C` placed in degree `0`, the object
in position `(p, q)` on page 2 of
`hyperextSpectralSequence TStructure.t K ((singleFunctor C 0).obj W)` is
`Ext^p(H^{-q}(K), W)` for `p : ℕ` (`secondPageExtIso`), and is zero for `p < 0`
(`isZero_secondPage_of_neg`).

The main step is an isomorphism `heartPieceIso K q` from `heartPiece TStructure.t K q` to the
cohomology object `H^{-q}(K)` placed in degree `-q`. It combines three facts.

* Two distinguished triangles, images of truncation triangles for `opTStructure t`, relate
  `heartPiece t K q` and `K` through the truncation `upperPiece t K q` of `K` in degrees `≥ -q`
  (`upperTriangle`, `heartTriangle`; generic in a pretriangulated category). In the derived
  category, the maps `heartPieceToUpperPiece` and `toUpperPiece` induce isomorphisms on `H^{-q}`
  (`heartPieceHomologyIso`).
* An object `X` lying in degrees `≥ n` and `≤ n` is isomorphic to `H^n(X)` placed in degree `n`
  (`isoSingleHomology`), by the unique morphism inducing the inverse of the canonical
  identification on `H^n` (`homologyFunctor_map_isoSingleHomology_hom`, `eq_isoSingleHomology_hom`).
* `heartPiece TStructure.t K q` lies in degrees `≥ -q` and `≤ -q`.

`secondPageExtAddEquiv` then moves the shift by `q` and applies `Abelian.Ext.homAddEquiv`.

Convergence of the spectral sequence is not proved.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
  CategoryTheory.Pretriangulated.Opposite CategoryTheory.Triangulated Opposite

namespace Langlands.Cohomology

namespace HyperextSpectralSequence

section Generic

universe v u

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasZeroObject C] [HasShift C ℤ]
  [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]

/-- The truncation of `K` in degrees `≥ -q` for `t`: the image in `C` of the truncation
`τ_{< q + 1} (op K)` for `opTStructure t`. -/
def upperPiece (t : TStructure C) (K : C) (q : ℤ) : C :=
  (((opTStructure t).truncLT (q + 1)).obj (op K)).unop

/-- The map `K ⟶ upperPiece t K q`, the image in `C` of the truncation map
`τ_{< q + 1} (op K) ⟶ op K` for `opTStructure t`. -/
def toUpperPiece (t : TStructure C) (K : C) (q : ℤ) : K ⟶ upperPiece t K q :=
  (((opTStructure t).truncLTι (q + 1)).app (op K)).unop

/-- The map `heartPiece t K q ⟶ upperPiece t K q`, the image in `C` of the truncation map
`τ_{< q + 1} (op K) ⟶ τ_{≥ q} τ_{< q + 1} (op K)` for `opTStructure t`. -/
def heartPieceToUpperPiece (t : TStructure C) (K : C) (q : ℤ) :
    heartPiece t K q ⟶ upperPiece t K q :=
  (((opTStructure t).truncGEπ q).app (((opTStructure t).truncLT (q + 1)).obj (op K))).unop

/-- The distinguished triangle of `C` whose second morphism is `toUpperPiece t K q`: the image
under `triangleOpEquivalence` of the truncation triangle of `op K` at `q + 1` for
`opTStructure t`. Its first object lies in `t.le (-q - 1)`. -/
def upperTriangle (t : TStructure C) (K : C) (q : ℤ) : Triangle C :=
  ((triangleOpEquivalence C).inverse.obj (((opTStructure t).triangleLTGE (q + 1)).obj (op K))).unop

lemma upperTriangle_distinguished (t : TStructure C) (K : C) (q : ℤ) :
    upperTriangle t K q ∈ distTriang C :=
  unop_distinguished _ ((opTStructure t).triangleLTGE_distinguished (q + 1) (op K))

lemma upperTriangle_mor₂ (t : TStructure C) (K : C) (q : ℤ) :
    (upperTriangle t K q).mor₂ = toUpperPiece t K q := rfl

instance upperTriangle_obj₁_isLE (t : TStructure C) (K : C) (q : ℤ) :
    t.IsLE (upperTriangle t K q).obj₁ (-(q + 1)) :=
  (opTStructure_isGE_iff t (((opTStructure t).truncGE (q + 1)).obj (op K)) (q + 1)).1
    inferInstance

/-- The distinguished triangle of `C` whose first morphism is `heartPieceToUpperPiece t K q`:
the image under `triangleOpEquivalence` of the truncation triangle at `q` of
`τ_{< q + 1} (op K)` for `opTStructure t`. Its third object lies in `t.ge (1 - q)`. -/
def heartTriangle (t : TStructure C) (K : C) (q : ℤ) : Triangle C :=
  ((triangleOpEquivalence C).inverse.obj
    (((opTStructure t).triangleLTGE q).obj (((opTStructure t).truncLT (q + 1)).obj (op K)))).unop

lemma heartTriangle_distinguished (t : TStructure C) (K : C) (q : ℤ) :
    heartTriangle t K q ∈ distTriang C :=
  unop_distinguished _ ((opTStructure t).triangleLTGE_distinguished q _)

lemma heartTriangle_mor₁ (t : TStructure C) (K : C) (q : ℤ) :
    (heartTriangle t K q).mor₁ = heartPieceToUpperPiece t K q := rfl

instance heartTriangle_obj₃_isGE (t : TStructure C) (K : C) (q : ℤ) :
    t.IsGE (heartTriangle t K q).obj₃ (-(q - 1)) :=
  (opTStructure_isLE_iff t (((opTStructure t).truncLT q).obj
    (((opTStructure t).truncLT (q + 1)).obj (op K))) (q - 1)).1 inferInstance

/-- Precomposition with an isomorphism `e : X ≅ X'`, as an additive equivalence
`(X' ⟶ Y) ≃+ (X ⟶ Y)`. -/
def precompAddEquiv {X X' : C} (e : X ≅ X') (Y : C) : (X' ⟶ Y) ≃+ (X ⟶ Y) where
  toFun f := e.hom ≫ f
  invFun g := e.inv ≫ g
  left_inv f := by simp
  right_inv g := by simp
  map_add' f g := by simp

/-- Postcomposition with an isomorphism `e : Y ≅ Y'`, as an additive equivalence
`(X ⟶ Y) ≃+ (X ⟶ Y')`. -/
def postcompAddEquiv (X : C) {Y Y' : C} (e : Y ≅ Y') : (X ⟶ Y) ≃+ (X ⟶ Y') where
  toFun f := f ≫ e.hom
  invFun g := g ≫ e.inv
  left_inv f := by simp
  right_inv g := by simp
  map_add' f g := by simp

/-- The shift functor by `n` as an additive equivalence `(X ⟶ Y) ≃+ (X⟦n⟧ ⟶ Y⟦n⟧)`. -/
def shiftAddEquiv (X Y : C) (n : ℤ) : (X ⟶ Y) ≃+ (X⟦n⟧ ⟶ Y⟦n⟧) :=
  AddEquiv.ofBijective (shiftFunctor C n).mapAddHom
    ⟨(shiftFunctor C n).map_injective, (shiftFunctor C n).map_surjective⟩

end Generic

section Derived

universe w' w v u

variable {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]

open DerivedCategory

/-- In the derived category, `toUpperPiece` induces an isomorphism on cohomology in
degree `-q`. -/
instance isIso_homologyMap_toUpperPiece (K : DerivedCategory C) (q : ℤ) :
    IsIso ((homologyFunctor C (-q)).map (toUpperPiece TStructure.t K q)) := by
  have hT := upperTriangle_distinguished (TStructure.t : TStructure (DerivedCategory C)) K q
  have hZ : IsZero ((homologyFunctor C (-q)).obj (upperTriangle TStructure.t K q).obj₁) :=
    isZero_of_isLE _ (-(q + 1)) (-q) (by lia)
  have hZ' : IsZero ((homologyFunctor C (-q + 1)).obj (upperTriangle TStructure.t K q).obj₁) :=
    isZero_of_isLE _ (-(q + 1)) (-q + 1) (by lia)
  have hm : Mono ((homologyFunctor C (-q)).map (upperTriangle TStructure.t K q).mor₂) :=
    ((homologyFunctor C 0).homologySequence_mono_shift_map_mor₂_iff _ hT (-q)).2
      (hZ.eq_of_src _ _)
  have he : Epi ((homologyFunctor C (-q)).map (upperTriangle TStructure.t K q).mor₂) :=
    ((homologyFunctor C 0).homologySequence_epi_shift_map_mor₂_iff _ hT (-q) (-q + 1) rfl).2
      (hZ'.eq_of_tgt _ _)
  exact @isIso_of_mono_of_epi _ _ _ _ _ _ hm he

/-- In the derived category, `heartPieceToUpperPiece` induces an isomorphism on cohomology in
degree `-q`. -/
instance isIso_homologyMap_heartPieceToUpperPiece (K : DerivedCategory C) (q : ℤ) :
    IsIso ((homologyFunctor C (-q)).map (heartPieceToUpperPiece TStructure.t K q)) := by
  have hT := heartTriangle_distinguished (TStructure.t : TStructure (DerivedCategory C)) K q
  have hZ : IsZero ((homologyFunctor C (-q)).obj (heartTriangle TStructure.t K q).obj₃) :=
    isZero_of_isGE _ (-(q - 1)) (-q) (by lia)
  have hZ' : IsZero ((homologyFunctor C (-q - 1)).obj (heartTriangle TStructure.t K q).obj₃) :=
    isZero_of_isGE _ (-(q - 1)) (-q - 1) (by lia)
  have hm : Mono ((homologyFunctor C (-q)).map (heartTriangle TStructure.t K q).mor₁) :=
    ((homologyFunctor C 0).homologySequence_mono_shift_map_mor₁_iff _ hT (-q - 1) (-q)
      (by lia)).2 (hZ'.eq_of_src _ _)
  have he : Epi ((homologyFunctor C (-q)).map (heartTriangle TStructure.t K q).mor₁) :=
    ((homologyFunctor C 0).homologySequence_epi_shift_map_mor₁_iff _ hT (-q)).2
      (hZ.eq_of_tgt _ _)
  exact @isIso_of_mono_of_epi _ _ _ _ _ _ hm he

/-- Two morphisms between objects in the image of `singleFunctor C n` are equal if they
induce the same morphism on cohomology in degree `n`. -/
lemma singleFunctor_hom_ext {A B : C} {n : ℤ}
    (f₁ f₂ : (singleFunctor C n).obj A ⟶ (singleFunctor C n).obj B)
    (h : (homologyFunctor C n).map f₁ = (homologyFunctor C n).map f₂) : f₁ = f₂ := by
  obtain ⟨a₁, rfl⟩ := (singleFunctor C n).map_surjective f₁
  obtain ⟨a₂, rfl⟩ := (singleFunctor C n).map_surjective f₂
  have h₁ : (homologyFunctor C n).map ((singleFunctor C n).map a₁) ≫
      (singleFunctorCompHomologyFunctorIso C n).hom.app B =
        (singleFunctorCompHomologyFunctorIso C n).hom.app A ≫ a₁ :=
    (singleFunctorCompHomologyFunctorIso C n).hom.naturality a₁
  have h₂ : (homologyFunctor C n).map ((singleFunctor C n).map a₂) ≫
      (singleFunctorCompHomologyFunctorIso C n).hom.app B =
        (singleFunctorCompHomologyFunctorIso C n).hom.app A ≫ a₂ :=
    (singleFunctorCompHomologyFunctorIso C n).hom.naturality a₂
  have : a₁ = a₂ := by
    rw [← cancel_epi ((singleFunctorCompHomologyFunctorIso C n).hom.app A), ← h₁, ← h₂, h]
  rw [this]

/-- An isomorphism from an object `X` of the derived category lying in degrees `≥ n` and `≤ n` to
an object in the image of `singleFunctor C n`, chosen by
`exists_iso_singleFunctor_obj_of_isGE_of_isLE`. Only an auxiliary step of `isoSingleHomology`,
which does not depend on this choice. -/
def chosenSingleIso (X : DerivedCategory C) (n : ℤ) [X.IsGE n] [X.IsLE n] :
    X ≅ (singleFunctor C n).obj (exists_iso_singleFunctor_obj_of_isGE_of_isLE X n).choose :=
  (exists_iso_singleFunctor_obj_of_isGE_of_isLE X n).choose_spec.some

/-- An object `X` of the derived category lying in degrees `≥ n` and `≤ n` is isomorphic to its
cohomology object in degree `n`, placed in degree `n`. The isomorphism is built from the chosen
isomorphism `chosenSingleIso X n`; it does not depend on that choice, since it is the unique
morphism inducing the canonical identification on cohomology in degree `n`
(`homologyFunctor_map_isoSingleHomology_hom`, `eq_isoSingleHomology_hom`). -/
def isoSingleHomology (X : DerivedCategory C) (n : ℤ) [X.IsGE n] [X.IsLE n] :
    X ≅ (singleFunctor C n).obj ((homologyFunctor C n).obj X) :=
  chosenSingleIso X n ≪≫
    (singleFunctor C n).mapIso
      (((singleFunctorCompHomologyFunctorIso C n).app _).symm ≪≫
        (homologyFunctor C n).mapIso (chosenSingleIso X n).symm)

/-- On cohomology in degree `n`, `isoSingleHomology X n` induces the inverse of the canonical
isomorphism `H^n((singleFunctor C n).obj (H^n X)) ≅ H^n X`. -/
lemma homologyFunctor_map_isoSingleHomology_hom (X : DerivedCategory C) (n : ℤ)
    [X.IsGE n] [X.IsLE n] :
    (homologyFunctor C n).map (isoSingleHomology X n).hom ≫
      (singleFunctorCompHomologyFunctorIso C n).hom.app ((homologyFunctor C n).obj X) = 𝟙 _ := by
  have key : ∀ {Y : C} (e : X ≅ (singleFunctor C n).obj Y),
      (homologyFunctor C n).map (e.hom ≫ (singleFunctor C n).map
        ((singleFunctorCompHomologyFunctorIso C n).inv.app Y ≫ (homologyFunctor C n).map e.inv)) ≫
          (singleFunctorCompHomologyFunctorIso C n).hom.app ((homologyFunctor C n).obj X) =
        𝟙 _ := by
    intro Y e
    have h := (singleFunctorCompHomologyFunctorIso C n).hom.naturality
      ((singleFunctorCompHomologyFunctorIso C n).inv.app Y ≫ (homologyFunctor C n).map e.inv)
    dsimp only [Functor.comp_map, Functor.id_map, Functor.id_obj] at h
    rw [CategoryTheory.Functor.map_comp, Category.assoc, h, Iso.hom_inv_id_app_assoc,
      ← CategoryTheory.Functor.map_comp, Iso.hom_inv_id, CategoryTheory.Functor.map_id]
  exact key (chosenSingleIso X n)

/-- `isoSingleHomology X n` is the only morphism `X ⟶ (singleFunctor C n).obj (H^n X)` inducing
the inverse of the canonical isomorphism on cohomology in degree `n`. -/
lemma eq_isoSingleHomology_hom (X : DerivedCategory C) (n : ℤ) [X.IsGE n] [X.IsLE n]
    (f : X ⟶ (singleFunctor C n).obj ((homologyFunctor C n).obj X))
    (hf : (homologyFunctor C n).map f ≫
      (singleFunctorCompHomologyFunctorIso C n).hom.app ((homologyFunctor C n).obj X) = 𝟙 _) :
    f = (isoSingleHomology X n).hom := by
  have h : (homologyFunctor C n).map f = (homologyFunctor C n).map (isoSingleHomology X n).hom :=
    (cancel_mono _).1 (hf.trans (homologyFunctor_map_isoSingleHomology_hom X n).symm)
  have : (isoSingleHomology X n).inv ≫ f =
      (isoSingleHomology X n).inv ≫ (isoSingleHomology X n).hom :=
    singleFunctor_hom_ext _ _ (by rw [CategoryTheory.Functor.map_comp,
      CategoryTheory.Functor.map_comp, h])
  exact (cancel_epi (isoSingleHomology X n).inv).1 this

/-- The comparison isomorphism `H^{-q}(heartPiece t K q) ≅ H^{-q}(K)` for the standard
t-structure on the derived category: the composite of the isomorphism induced by
`heartPieceToUpperPiece` with the inverse of the isomorphism induced by `toUpperPiece`. -/
def heartPieceHomologyIso (K : DerivedCategory C) (q : ℤ) :
    (homologyFunctor C (-q)).obj (heartPiece TStructure.t K q) ≅
      (homologyFunctor C (-q)).obj K :=
  asIso ((homologyFunctor C (-q)).map (heartPieceToUpperPiece TStructure.t K q)) ≪≫
    (asIso ((homologyFunctor C (-q)).map (toUpperPiece TStructure.t K q))).symm

/-- For the standard t-structure on the derived category, `heartPiece TStructure.t K q` is
isomorphic to the cohomology object `H^{-q}(K)` placed in degree `-q`. -/
def heartPieceIso (K : DerivedCategory C) (q : ℤ) :
    heartPiece TStructure.t K q ≅ (singleFunctor C (-q)).obj ((homologyFunctor C (-q)).obj K) :=
  isoSingleHomology _ (-q) ≪≫ (singleFunctor C (-q)).mapIso (heartPieceHomologyIso K q)

/-- On cohomology in degree `-q`, `heartPieceIso K q` induces `heartPieceHomologyIso K q`,
followed by the inverse of the canonical isomorphism
`H^{-q}((singleFunctor C (-q)).obj (H^{-q} K)) ≅ H^{-q} K`. -/
lemma homologyFunctor_map_heartPieceIso_hom (K : DerivedCategory C) (q : ℤ) :
    (homologyFunctor C (-q)).map (heartPieceIso K q).hom ≫
      (singleFunctorCompHomologyFunctorIso C (-q)).hom.app ((homologyFunctor C (-q)).obj K) =
        (heartPieceHomologyIso K q).hom := by
  have h := (singleFunctorCompHomologyFunctorIso C (-q)).hom.naturality
    (heartPieceHomologyIso K q).hom
  dsimp only [Functor.comp_map, Functor.id_map] at h
  simp only [heartPieceIso, Iso.trans_hom, Functor.mapIso_hom, CategoryTheory.Functor.map_comp,
    Category.assoc]
  rw [h, ← Category.assoc, homologyFunctor_map_isoSingleHomology_hom, Category.id_comp]

/-- The additive equivalence `Hom(heartPiece t K q, W⟦p + q⟧) ≃+ Ext^p(H^{-q}(K), W)` for the
standard t-structure `t` on the derived category, an object `W` of `C` placed in degree `0` and
`p : ℕ`. Writing `M = H^{-q}(K)`, it precomposes with the inverse of `heartPieceIso K q` and with
the isomorphism `((singleFunctor C 0).obj M)⟦q⟧ ≅ (singleFunctor C (-q)).obj M`, postcomposes
with `W⟦p + q⟧ ≅ W⟦p⟧⟦q⟧`, undoes the shift by `q`, and applies the inverse of
`Abelian.Ext.homAddEquiv`. -/
def secondPageExtAddEquiv [HasExt.{w'} C] (K : DerivedCategory C) (W : C) (p : ℕ) (q : ℤ) :
    (heartPiece TStructure.t K q ⟶ ((singleFunctor C 0).obj W)⟦(p : ℤ) + q⟧) ≃+
      Abelian.Ext.{w'} ((homologyFunctor C (-q)).obj K) W p :=
  (precompAddEquiv (heartPieceIso K q).symm _).trans <|
    (precompAddEquiv (((singleFunctors C).shiftIso q (-q) 0 (by lia)).app
      ((homologyFunctor C (-q)).obj K)) _).trans <|
    (postcompAddEquiv _ ((shiftFunctorAdd' (DerivedCategory C) (p : ℤ) q ((p : ℤ) + q) rfl).app
      ((singleFunctor C 0).obj W))).trans <|
    (shiftAddEquiv ((singleFunctor C 0).obj ((homologyFunctor C (-q)).obj K))
      (((singleFunctor C 0).obj W)⟦(p : ℤ)⟧) q).symm.trans Abelian.Ext.homAddEquiv.symm

/-- For the standard t-structure on the derived category and an object `W` of `C` placed in
degree `0`, the object in position `(p, q)`, `p : ℕ`, on page 2 of the hyperext spectral sequence
is `Ext^p(H^{-q}(K), W)`. -/
def secondPageExtIso [HasExt.{w} C] (K : DerivedCategory C) (W : C) (p : ℕ) (q : ℤ) :
    ((hyperextSpectralSequence TStructure.t K ((singleFunctor C 0).obj W)).page 2).X ⟨p, q⟩ ≅
      AddCommGrpCat.of (Abelian.Ext.{w} ((homologyFunctor C (-q)).obj K) W p) :=
  secondPageIso TStructure.t K ((singleFunctor C 0).obj W) p q ≪≫
    (secondPageExtAddEquiv K W p q).toAddCommGrpIso

/-- For an object `W` of `C` placed in degree `0`, the objects in positions `(p, q)` with `p < 0`
on page 2 of the hyperext spectral sequence are zero. -/
lemma isZero_secondPage_of_neg (K : DerivedCategory C) (W : C) (p q : ℤ) (hp : p < 0) :
    IsZero (((hyperextSpectralSequence TStructure.t K ((singleFunctor C 0).obj W)).page 2).X
      ⟨p, q⟩) := by
  refine IsZero.of_iso ?_ (secondPageIso TStructure.t K ((singleFunctor C 0).obj W) p q)
  have : TStructure.t.IsGE (((singleFunctor C 0).obj W)⟦p + q⟧) (-(p + q)) :=
    TStructure.t.isGE_shift _ 0 (p + q) (-(p + q)) (by lia)
  have : Subsingleton (heartPiece TStructure.t K q ⟶ ((singleFunctor C 0).obj W)⟦p + q⟧) :=
    ⟨fun f g => (TStructure.t.zero_of_isLE_of_isGE f (-q) (-(p + q)) (by lia) inferInstance
      this).trans (TStructure.t.zero_of_isLE_of_isGE g (-q) (-(p + q)) (by lia) inferInstance
        this).symm⟩
  exact AddCommGrpCat.isZero_of_iff_subsingleton.2 this

end Derived

end HyperextSpectralSequence

end Langlands.Cohomology
