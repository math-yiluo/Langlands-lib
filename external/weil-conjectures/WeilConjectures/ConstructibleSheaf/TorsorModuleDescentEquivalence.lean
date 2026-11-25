/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.ConstructibleSheaf.Defs
public import WeilConjectures.AlgebraicGeometry.Morphisms.EtaleTorsor
public import Mathlib.RepresentationTheory.Rep.Basic
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Algebra.Field.ULift
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings

public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
import WeilConjectures.ConstructibleSheaf.TorsorAssociatedModuleComparisons
import WeilConjectures.ConstructibleSheaf.TorsorAssociatedModuleFull
import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtalePoint
import WeilConjectures.Mathlib.CategoryTheory.Sites.Point.ConstantSheaf
import WeilConjectures.ConstructibleSheaf.TorsorAssociatedModuleEssentialImage

/-!
# Descent equivalence for a connected finite torsor

Source: Stacks Project, Tags 0DV5 (3), 0DV6, 0A3R, 04TR and 04TS.
(blueprint: lem-weil-pbc-torsor-module-descent-equivalence)
-/

@[expose] public section

set_option autoImplicit false
universe u
open CategoryTheory Limits
namespace AlgebraicGeometry
open Etale

/-- Representations are equivalent to all module sheaves trivialized by a connected
finite torsor. The underlying functor is additive, its pullback is naturally constant,
and the trivial rank-one representation descends to the coefficient sheaf.
Source: Stacks Project, Tags 0DV5 (3), 0DV6 and 0A3R; sites.tex, Tags 04TR and 04TS.
(blueprint: lem-weil-pbc-torsor-module-descent-equivalence)

Proof:
1. Construct the associated sheaf directly. For a P-representation N, restrict its scalars along
ULift(F_l) -> F_l. For W etale over V, take the submodule of locally constant sections on W
times_V c.P with values in this module satisfying s(g*y)=g*s(y). The torsor action and
representation action make this a submodule. Restriction is restriction of sections. Given a
matching family on an etale cover of W, glue its sections on the induced cover upstairs;
uniqueness of gluing preserves equivariance. This proves the sheaf condition. On the pulled-back
torsor there is a diagonal section, and evaluation at it identifies equivariant sections with
ordinary constant-sheaf sections. Its inverse extends a section by the group action. These
formulas commute with restriction and module maps and give the natural pullback isomorphism.
2. An equivariant linear map acts pointwise on these sections. Pointwise identity, composition
and addition prove functoriality and additivity. For the trivial rank-one representation the
equivariance condition is invariance. A locally constant invariant function on W times_V c.P is
the pullback of a unique locally constant function on W: define it on an etale cover where the
torsor has a section, and use invariance to make these local definitions independent of the
section and equal on overlaps. Hence the trivial coefficient representation maps to the constant
coefficient sheaf.
3. For a sheaf F whose pullback is constant with value A, choose a trivialization. On the
components of c.P times_V c.P indexed by P, the transported canonical descent isomorphism is a
map of constant module sheaves on c.P. Each constant section a has locally constant image;
connectedness and nonemptiness imply that image is constant. Evaluation at one point recovers a
linear map on A. Equality of the constant sections implies equality of sheaf maps since sections
are locally constant sections. The inverse descent map gives invertibility, and the
triple-overlap cocycle gives the group action (with the projection convention of the
construction). Transporting scalars back gives a representation. Local evaluation in the
trivialization identifies its associated sheaf with F, and these local identifications agree by
the transported descent maps. This proves essential surjectivity without finite-dimensionality.
4. For a map between two associated sheaves, pull it back and use the natural constant pullback
identifications. The same connectedness argument shows it is one linear map of values.
Commutation with the canonical descent maps says precisely that this linear map is
P-equivariant. Its pointwise map of associated sheaves is the original map, because they agree
after the etale surjective covering c.P -> V, and uniqueness in the sheaf condition detects that
equality. This gives full faithfulness. Together with essential surjectivity it yields an
equivalence with the full subcategory of sheaves having constant pullback; choose its inverse
and unit and counit from these object and morphism identifications. The underlying functor
retains its additivity, pullback comparison and trivial coefficient comparison.
The zero module and the trivial group require no exceptions. -/
theorem Scheme.GaloisCover.exists_module_descent_equivalence
    {V : Scheme.{u}} [ConnectedSpace V] (ℓ : ℕ) [Fact ℓ.Prime]
    (P : Type u) [Group P] [Finite P]
    (c : Scheme.GaloisCover (ULift.{u + 1} P) V) [ConnectedSpace c.P] :
    let C := ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ))
    let D : ObjectProperty (Sheaf V.smallEtaleTopology C) := fun F ↦
      ∃ A : C, Nonempty ((c.π)^*[C].obj F ≅
        (constantSheaf c.P.smallEtaleTopology C).obj A)
    ∃ E : Rep.{u + 1} (ZMod ℓ) P ≌ D.FullSubcategory,
      let T := E.functor ⋙ D.ι
      T.Additive ∧
      Nonempty (T ⋙ (c.π)^*[C] ≅
        forget₂ (Rep.{u + 1} (ZMod ℓ) P) (ModuleCat.{u + 1} (ZMod ℓ)) ⋙
          ModuleCat.restrictScalars.{u + 1}
            (ULift.ringEquiv.toRingHom : ULift.{u + 1} (ZMod ℓ) →+* ZMod ℓ) ⋙
          constantSheaf c.P.smallEtaleTopology C) ∧
      Nonempty (T.obj (Rep.trivial (ZMod ℓ) P (ULift.{u + 1} (ZMod ℓ))) ≅
        (constantSheaf V.smallEtaleTopology C).obj
          (ModuleCat.of _ (ULift.{u + 1} (ZMod ℓ)))) := by
  classical
  dsimp only
  let C := ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ))
  let D : ObjectProperty (Sheaf V.smallEtaleTopology C) := fun F ↦
    ∃ A : C, Nonempty ((c.π)^*[C].obj F ≅
      (constantSheaf c.P.smallEtaleTopology C).obj A)
  let T := c.associatedModuleFunctor ℓ
  obtain ⟨⟨eπ⟩, hunit⟩ := c.associatedModuleFunctor_comparisons ℓ P
  let _ : T.Full := c.associatedModuleFunctor_full ℓ P
  obtain ⟨x⟩ := ‹ConnectedSpace c.P›.toNonempty
  let Φ := c.P.uliftPointSmallEtale x
  let _ : (constantSheaf c.P.smallEtaleTopology C).Faithful :=
    Functor.Faithful.of_comp_iso (Φ.constantSheafCompSheafFiberIso _ C)
  let _ : (T ⋙ (c.π)^*[C]).Faithful := Functor.Faithful.of_iso eπ.symm
  let _ : T.Faithful := Functor.Faithful.of_comp T (c.π)^*[C]
  have hT : ∀ N, D (T.obj N) := fun N ↦
    ⟨_, ⟨eπ.app N⟩⟩
  let L := D.lift T hT
  have hess : L.EssSurj := by
    constructor
    intro F
    obtain ⟨A, hA⟩ := F.property
    obtain ⟨N, ⟨e⟩⟩ := c.associatedModuleFunctor_essentialImage ℓ P F.obj A hA
    exact ⟨N, ⟨D.isoMk e⟩⟩
  let _ : L.EssSurj := hess
  let _ : L.IsEquivalence := {}
  let E := L.asEquivalence
  refine ⟨E, ?_, ?_, ?_⟩
  · change (L ⋙ D.ι).Additive
    exact Functor.additive_of_iso (D.liftCompιIso T hT).symm
  · exact ⟨eπ⟩
  · exact hunit

end AlgebraicGeometry
