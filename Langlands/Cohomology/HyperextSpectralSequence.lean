import Mathlib.Algebra.Homology.SpectralObject.SpectralSequence
import Mathlib.CategoryTheory.Triangulated.Opposite.Triangulated
import Mathlib.CategoryTheory.Triangulated.TStructure.SpectralObject
import Mathlib.CategoryTheory.Triangulated.Yoneda

/-!
# The hyperext spectral sequence of a t-structure

Let `t` be a t-structure on a triangulated category `C` and let `K`, `B` be objects of `C`.
Applying the cohomological functor `Hom(-, B)` to the truncations of `K` gives a cohomological
spectral sequence of abelian groups, starting on page 2, with

* `E₂^{p,q} = Hom(heartPiece t K q, B⟦p + q⟧)` (`secondPageIso`), where `heartPiece t K q` is a
  truncation of `K` lying in `t.le (-q)` and in `t.ge (-q)` (`heartPiece_isLE`,
  `heartPiece_isGE`);
* differentials of bidegree `(r, 1 - r)` on page `r`;
* in total degree `n`, the term `Hom(K, B⟦n⟧)` of the underlying spectral object
  (`abutmentIso`), the intended abutment.

The construction uses Mathlib's spectral objects. A t-structure on `Cᵒᵖ` is obtained from `t`
by exchanging the two halves and negating degrees (`opTStructure`). Its spectral object at
`op K` (`TStructure.spectralObject`) is a spectral object in `Cᵒᵖ`; the homological functor
`preadditiveYoneda.obj B : Cᵒᵖ ⥤ AddCommGrpCat` sends it to a spectral object in abelian groups
(`hyperextSpectralObject`), and `Abelian.SpectralObject.E₂SpectralSequence` turns that into a
spectral sequence (`hyperextSpectralSequence`).

Convergence of the spectral sequence to `Hom(K, B⟦p + q⟧)` is not proved here: Mathlib has no
convergence theory for these spectral sequences. The identification of `E₂^{p,q}` with
`Ext^p(H^{-q} K, B)` for the standard t-structure on a derived category is not made here
either.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
  CategoryTheory.Pretriangulated.Opposite CategoryTheory.Triangulated Opposite

namespace Langlands.Cohomology

namespace HyperextSpectralSequence

universe v u

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasZeroObject C] [HasShift C ℤ]
  [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]

/-- The t-structure on `Cᵒᵖ` opposite to `t`: an object `X` of `Cᵒᵖ` lies in degrees `≤ n`
if `X.unop` lies in degrees `≥ -n` for `t`, and in degrees `≥ n` if `X.unop` lies in degrees
`≤ -n` for `t`. Here `Cᵒᵖ` carries Mathlib's pretriangulated structure: shifting by `n` on
`Cᵒᵖ` corresponds to shifting by `-n` on `C`, and the distinguished triangles of `Cᵒᵖ` are the
images of the distinguished triangles of `C` under `triangleOpEquivalence`. -/
def opTStructure (t : TStructure C) : TStructure Cᵒᵖ where
  le n X := t.ge (-n) X.unop
  ge n X := t.le (-n) X.unop
  le_isClosedUnderIsomorphisms n :=
    ⟨fun e hX => (t.ge (-n)).prop_of_iso e.unop.symm hX⟩
  ge_isClosedUnderIsomorphisms n :=
    ⟨fun e hX => (t.le (-n)).prop_of_iso e.unop.symm hX⟩
  le_shift n a n' h X hX := t.ge_shift (-n) (-a) (-n') (by lia) X.unop hX
  ge_shift n a n' h X hX := t.le_shift (-n) (-a) (-n') (by lia) X.unop hX
  zero' X Y f hX hY :=
    Quiver.Hom.unop_inj (t.zero_of_isLE_of_isGE f.unop (-1) 0 (by lia) ⟨hY⟩
      ⟨by simpa using hX⟩)
  le_zero_le X hX := t.ge_antitone (show (-1 : ℤ) ≤ -0 by lia) _ hX
  ge_one_le X hX := t.le_monotone (show (-1 : ℤ) ≤ -0 by lia) _ hX
  exists_triangle_zero_one A := by
    obtain ⟨X, Y, hX, hY, f, g, h, mem⟩ := t.exists_triangle A.unop (-1) 0 (by lia)
    exact ⟨_, _, (by simpa using hY), hX, _, _, _, op_distinguished _ mem⟩

lemma opTStructure_le_iff (t : TStructure C) (n : ℤ) (X : Cᵒᵖ) :
    (opTStructure t).le n X ↔ t.ge (-n) X.unop := Iff.rfl

lemma opTStructure_ge_iff (t : TStructure C) (n : ℤ) (X : Cᵒᵖ) :
    (opTStructure t).ge n X ↔ t.le (-n) X.unop := Iff.rfl

lemma opTStructure_isLE_iff (t : TStructure C) (X : Cᵒᵖ) (n : ℤ) :
    (opTStructure t).IsLE X n ↔ t.IsGE X.unop (-n) :=
  ⟨fun h => ⟨h.le⟩, fun h => ⟨h.ge⟩⟩

lemma opTStructure_isGE_iff (t : TStructure C) (X : Cᵒᵖ) (n : ℤ) :
    (opTStructure t).IsGE X n ↔ t.IsLE X.unop (-n) :=
  ⟨fun h => ⟨h.ge⟩, fun h => ⟨h.le⟩⟩

/-- The truncation of `K` used for the `q`-th row of the hyperext spectral sequence: the image
in `C` of the truncation `τ_{≥ q} τ_{< q + 1} (op K)` for `opTStructure t` (`op_heartPiece`),
written with Mathlib's functor `TStructure.ω₁` as the spectral object does. It lies in
`t.le (-q)` and in `t.ge (-q)` (`heartPiece_isLE`, `heartPiece_isGE`). Classically it is
`τ_{≤ -q} τ_{≥ -q} K`, the cohomology object `H^{-q} K` of the heart placed in degree `-q`;
that identification is not formalized here. -/
def heartPiece (t : TStructure C) (K : C) (q : ℤ) : C :=
  ((((opTStructure t).ω₁.obj
    (ComposableArrows.mk₁ (homOfLE (show ((q : ℤ) : EInt) ≤ ((q + 1 : ℤ) : EInt) by simp)))).obj
      (op K))).unop

/-- The opposite of `heartPiece t K q` is the truncation of `op K` in degrees `[q, q + 1)` for
`opTStructure t`. -/
lemma op_heartPiece (t : TStructure C) (K : C) (q : ℤ) :
    op (heartPiece t K q) = ((opTStructure t).truncGELT q (q + 1)).obj (op K) := rfl

/-- `heartPiece t K q` lies in degrees `≤ -q` for `t`. -/
instance heartPiece_isLE (t : TStructure C) (K : C) (q : ℤ) :
    t.IsLE (heartPiece t K q) (-q) :=
  ((opTStructure_isGE_iff t (op (heartPiece t K q)) q).1
    ((opTStructure t).isGE_eTruncGE_obj_obj q q le_rfl _))

variable [IsTriangulated C]

/-- `heartPiece t K q` lies in degrees `≥ -q` for `t`. -/
instance heartPiece_isGE (t : TStructure C) (K : C) (q : ℤ) :
    t.IsGE (heartPiece t K q) (-q) := by
  rw [← opTStructure_isLE_iff t (op (heartPiece t K q)) q, op_heartPiece]
  have : (opTStructure t).IsLE (((opTStructure t).truncGELT q (q + 1)).obj (op K)) (q + 1 - 1) :=
    inferInstance
  simpa using this


/-- The spectral object in abelian groups obtained by applying the homological functor
`Hom(-, B)` on `Cᵒᵖ` to the spectral object of `op K` for `opTStructure t`. Its term
`H^n(a ⟶ b)` is the group of morphisms from the `opTStructure t`-truncation of `op K` in degrees
`[a, b)`, read in `C`, to `B⟦n⟧`. -/
def hyperextSpectralObject (t : TStructure C) (K B : C) :
    Abelian.SpectralObject AddCommGrpCat.{v} EInt :=
  ((opTStructure t).spectralObject (op K)).mapHomologicalFunctor (preadditiveYoneda.obj B)

/-- The hyperext spectral sequence of `K` and `B` for the t-structure `t`: Mathlib's
`E₂`-cohomological spectral sequence of `hyperextSpectralObject t K B`, with objects indexed by
`ℤ × ℤ` and differentials of bidegree `(r, 1 - r)` on page `r`. -/
def hyperextSpectralSequence (t : TStructure C) (K B : C) :
    E₂CohomologicalSpectralSequence AddCommGrpCat.{v} :=
  (hyperextSpectralObject t K B).E₂SpectralSequence

/-- The term of `hyperextSpectralObject t K B` in degree `n` for the arrow `⊥ ⟶ ⊤` of `EInt` is
`Hom(K, B⟦n⟧)`, the intended abutment of the spectral sequence in total degree `n`; the two are
equal by definition. Convergence is not proved. -/
def abutmentIso (t : TStructure C) (K B : C) (n : ℤ) :
    ((hyperextSpectralObject t K B).H n).obj
      (ComposableArrows.mk₁ (homOfLE (show (⊥ : EInt) ≤ ⊤ from bot_le))) ≅
      AddCommGrpCat.of (K ⟶ B⟦n⟧) :=
  Iso.refl _

/-- The object in position `(p, q)` on page 2 of the hyperext spectral sequence is
`Hom(heartPiece t K q, B⟦p + q⟧)`. This composes Mathlib's description of the page objects
(`spectralSequencePageXIso`, giving `E^{p+q}(q ≤ q ≤ q + 1 ≤ q + 1)` on page 2) with
`EIsoH`, the identification of that term with `H^{p+q}(q ⟶ q + 1)`. -/
def secondPageIso (t : TStructure C) (K B : C) (p q : ℤ) :
    ((hyperextSpectralSequence t K B).page 2).X ⟨p, q⟩ ≅
      AddCommGrpCat.of (heartPiece t K q ⟶ B⟦p + q⟧) :=
  (hyperextSpectralObject t K B).spectralSequencePageXIso
      Abelian.SpectralObject.coreE₂Cohomological 2 (le_refl 2) ⟨p, q⟩
      (q : EInt) (q : EInt) ((q + 1 : ℤ) : EInt) ((q + 1 : ℤ) : EInt)
      (by simp) rfl rfl (by simp; lia) (p + q - 1) (p + q) (p + q + 1) rfl ≪≫
    (hyperextSpectralObject t K B).EIsoH
      (homOfLE (show ((q : ℤ) : EInt) ≤ ((q + 1 : ℤ) : EInt) by simp))
      (p + q - 1) (p + q) (p + q + 1) ≪≫ Iso.refl _

end HyperextSpectralSequence

end Langlands.Cohomology
