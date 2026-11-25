/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
import WeilConjectures.AlgebraicGeometry.StrictPerfectPackageOnSite

public import WeilConjectures.AlgebraicGeometry.LatticeClassPresheaf
import WeilConjectures.AlgebraicGeometry.LatticeGluedRationalizationIso

/-!
# Effective descent of embedded lattice pairs

Source: Bhatt--Scholze, Proposition 6.8.4(6), descent of embedded lattices
(auxiliary; not a blueprint node).
-/

@[expose] public section

attribute [local instance] AlgebraicGeometry.ProEtale.latticeWeakSheafifyOver
  AlgebraicGeometry.Scheme.strictPerfectSliceLocallyBijective

attribute [local instance] AlgebraicGeometry.ProEtale.restrictionStrongSheafifyOver
  AlgebraicGeometry.ProEtale.restrictionWeakSheafifyOverOver
  AlgebraicGeometry.ProEtale.restrictionWEqualsOverOver
  AlgebraicGeometry.ProEtale.restrictionStrongSheafifyOverOver

universe u

open CategoryTheory Opposite
open scoped ChangeOfRings

namespace AlgebraicGeometry.ProEtale

/-- A matching family of embedded lattice classes has a global lattice representative.
Source: Bhatt--Scholze, Proposition 6.8.4(6), pp. 59–60; descent of embedded lattices.
(auxiliary; not a blueprint node).
Proof: choose integral representatives of the given local image families. On every
common slice, compatibility identifies their image families. The image-classification
lemma gives an intertwining integral isomorphism, unique by injectivity of the
coefficient map. Uniqueness proves naturality of the transition maps and their
cocycle identities. Apply effective gluing of module sheaves on the covering sieve.
Refine the covering by the finite free basis covers of the local representatives;
this makes the glued integral module finite locally free. The local embeddings
into the fixed rational module agree and glue to an embedding. Its scalar extension
restricts, by the slice tensor comparison, to each given rationalization. Their
inverses agree on overlaps and glue to its inverse. The resulting lattice pair
has on each covering slice precisely the prescribed image family. This argument
allows varying rank, the zero module, and the empty covering of an empty object. -/
theorem exists_latticePair_of_compatible_classes
    {X : Scheme.{u}}
    {R S : Sheaf (Scheme.ProEt.topology X) CommRingCat.{u + 1}} (a : R ⟶ S)
    (L : SheafOfModules.{u + 1}
      ((sheafCompose _ (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj S))
    (ha : ∀ (U : X.ProEt) T,
      Function.Injective (((latticeScalarMap a U).hom.app T).hom))
    (U : X.ProEt) (r : Sieve U) (hr : r ∈ (Scheme.ProEt.topology X) U)
    (x : Presieve.FamilyOfElements (latticeClassPresheaf a L) r.arrows)
    (hx : x.Compatible) :
    ∃ P : IntegralLatticePair a L U,
      ∀ (V : X.ProEt) (f : V ⟶ U) (hf : r f) (T : Over V),
        P.image (op ((Over.map f).obj T)) = (x f hf).down.val T := by
  classical
  let e := gluedLatticeRationalization a L U ha r x hx hr
  let : IsIso e := gluedLatticeRationalization_isIso a L ha U r hr x hx
  let P : IntegralLatticePair a L U :=
    { module := gluedLatticeModule a L ha U r x hx
      locallyFree := gluedLatticeModule_finiteLocallyFree a L ha U r x hx hr
      rationalization := asIso e }
  refine ⟨P, ?_⟩
  intro V f hf T
  obtain ⟨Z, t, rfl⟩ := T.mk_surjective
  let i : latticeCoverIndex U r := ⟨V, f, hf⟩
  let W : Over U := Over.mk (t ≫ f)
  let b : W ⟶ latticeCoverObject U r i := Over.homMk t rfl
  have hmap (m : P.module.val.obj (op W)) :
      P.rationalization.hom.val.app (op W)
        (((PresheafOfModules.sheafificationAdjunction (𝟙 _)).unit.app
          (SheafOfModules.changeOfRingsPresheaf.{u, u + 1, u + 1}
            (latticeScalarMap a U) P.module)).app
          (op W) ((1 : (S.over U).obj.obj (op W)) ⊗ₜ[(R.over U).obj.obj (op W),
            ((latticeScalarMap a U).hom.app (op W)).hom] m)) =
      latticeCoverEmbedding a L U r x i W b
        ((gluedLatticeModuleLocalIso a L ha U r x hx i).hom.val.app
          (op (Over.mk b)) m) := by
    exact (rationalizeEmbedding_unit a L U _ _ (op W) m).trans
      (gluedLatticeEmbedding_spec a L U ha r x hx hr i W b m)
  change Set.range _ = _
  trans (latticeCoverPair a L U r x i).image (op (Over.mk t))
  · ext z
    constructor
    · rintro ⟨m, rfl⟩
      exact ⟨(gluedLatticeModuleLocalIso a L ha U r x hx i).hom.val.app
        (op (Over.mk b)) m, (hmap m).symm⟩
    · rintro ⟨m, rfl⟩
      let n := (gluedLatticeModuleLocalIso a L ha U r x hx i).inv.val.app
        (op (Over.mk b)) m
      have hn : (gluedLatticeModuleLocalIso a L ha U r x hx i).hom.val.app
          (op (Over.mk b)) n = m := by
        have h := congrArg (fun f ↦ f.val.app (op (Over.mk b)))
          (gluedLatticeModuleLocalIso a L ha U r x hx i).inv_hom_id
        exact ConcreteCategory.congr_hom h m
      exact ⟨n, (hmap n).trans (congrArg
        (latticeCoverEmbedding a L U r x i W b) hn)⟩
  · exact latticeCoverPair_image a L U r x i (Over.mk t)

end AlgebraicGeometry.ProEtale
