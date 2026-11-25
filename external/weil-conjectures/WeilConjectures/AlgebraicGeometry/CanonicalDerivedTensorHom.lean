/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.CanonicalDerivedTensorHomModel
import WeilConjectures.AlgebraicGeometry.CanonicalDerivedTensorHomMapExistence
import WeilConjectures.AlgebraicGeometry.CanonicalDerivedTensorHomMapBijective
import WeilConjectures.Algebra.Homology.KFlatResolution
import WeilConjectures.Algebra.Homology.KInjectiveHomComplex
import Mathlib.Algebra.Homology.DerivedCategory.KInjective

/-! # Canonical derived tensor/internal-Hom bijections
Source: Stacks Project, cohomology.tex, Tag 08DJ.
(blueprint: def-pc-canonical-derived-tensor-hom-bijection).
-/

@[expose] public section

set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe uCD wCD
open CategoryTheory CategoryTheory.MonoidalCategory Opposite TopologicalSpace
namespace AlgebraicGeometry

/-- Existence of the canonical tensor-Hom family.
Source: Stacks, cohomology.tex, Tag 08DJ
(blueprint: def-pc-canonical-derived-tensor-hom-bijection).
Proof: resolve both tensor inputs by K-flat complexes and the target by the fixed
K-injective functor. Curry the Hom-complex components using the sheaf tensor-Hom
bijection. The Hom differential and total-tensor signs make the displayed ψ a chain
map. Maps into a K-injective compute derived Hom; localization and the resolution
map give the displayed equation. Common resolutions show independence of choices,
and componentwise composition gives naturality in all three variables. -/
theorem exists_canonicalDerivedTensorHom (X : Scheme.{uCD})
    [HasDerivedCategory.{wCD} (SheafOfModules.{uCD} (moduleRings X.toRingedSpace))] :
    ∃ e : ∀ K L M : schemeDerivedCategory X,
      (K ⟶ (derivedInternalHom (Opens.grothendieckTopology X.toRingedSpace)
        X.toRingedSpace.sheaf).obj (op L, M)) ≃ (K ⊗ L ⟶ M),
      IsCanonicalDerivedTensorHom X e := by
  classical
  obtain ⟨t, ht⟩ := exists_canonicalDerivedTensorHomMap X
  have hb := canonicalDerivedTensorHomMap_bijective X t ht
  let e := fun K L M ↦ Equiv.ofBijective (t K L M) (hb K L M)
  refine ⟨e, ?_⟩
  change IsCanonicalDerivedTensorHomMap X (fun K L M ↦ (e K L M).toFun)
  exact ht

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
set_option linter.style.haveILetI false in
/-- Uniqueness of the family specified on representatives.
Source: Stacks, cohomology.tex, Tag 08DJ
(blueprint: def-pc-canonical-derived-tensor-hom-bijection).
Proof: on K-flat inputs, Hom(L,I(M)) is K-injective. Every derived morphism into
it is represented by a chain map up to homotopy. Its uncurrying is determined on
every tensor summand, so the representative equation determines the bijection.
Every derived object has such a representative; naturality transports the equality. -/
theorem IsCanonicalDerivedTensorHom.unique (X : Scheme.{uCD})
    [HasDerivedCategory.{wCD} (SheafOfModules.{uCD} (moduleRings X.toRingedSpace))]
    {e e' : ∀ K L M : schemeDerivedCategory X,
      (K ⟶ (derivedInternalHom (Opens.grothendieckTopology X.toRingedSpace)
        X.toRingedSpace.sheaf).obj (op L, M)) ≃ (K ⊗ L ⟶ M)}
    (h : IsCanonicalDerivedTensorHom X e)
    (h' : IsCanonicalDerivedTensorHom X e') : e = e' := by
  classical
  let C := SheafOfModules.{uCD} (moduleRings X.toRingedSpace)
  -- Share the sheafification and abelian instances throughout the proof.
  let : HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{uCD} := inferInstance
  have : (Opens.grothendieckTopology X).WEqualsLocallyBijective AddCommGrpCat.{uCD} :=
    inferInstance
  let : Abelian C := inferInstance
  let Q := DerivedCategory.Q.{wCD} (C := C)
  let H := derivedInternalHom (Opens.grothendieckTopology X.toRingedSpace)
    X.toRingedSpace.sheaf
  funext K L M
  apply Equiv.ext
  intro f
  -- Name the existential proofs before destructuring to avoid generalizing through the goal.
  have hPResolution :=
    CochainComplex.exists_isKFlatResolution (R := X.sheaf) (Q.objPreimage K)
  rcases hPResolution with ⟨P, p, hP, _, hp, _⟩
  have hLResolution :=
    CochainComplex.exists_isKFlatResolution (R := X.sheaf) (Q.objPreimage L)
  rcases hLResolution with ⟨Lc, l, hL, _, hl, _⟩
  have : IsIso (Q.map p) := (DerivedCategory.isIso_Q_map_iff_quasiIso _ p).2 hp
  have : IsIso (Q.map l) := (DerivedCategory.isIso_Q_map_iff_quasiIso _ l).2 hl
  let a : Q.obj P ≅ K := asIso (Q.map p) ≪≫ Q.objObjPreimageIso K
  let b : Q.obj Lc ≅ L := asIso (Q.map l) ≪≫ Q.objObjPreimageIso L
  let Mc := Q.objPreimage M
  let c : Q.obj Mc ≅ M := Q.objObjPreimageIso M
  let I := (schemeHomKInjectiveResolution X).obj Mc
  have : IsGrothendieckAbelian.{uCD} C := SheafOfModules.isGrothendieckAbelian _
  have : I.IsKInjective :=
    CochainComplex.isKInjective_kInjectiveResolutionFunctor_obj.{uCD} C Mc
  have : (homComplex (R := X.sheaf) Lc I).IsKInjective :=
    CochainComplex.isKInjective_homComplex_of_isKFlat (R := X.sheaf) Lc I hL
  let j := schemeDerivedInternalHomResolutionIso X Lc Mc
  let g : Q.obj P ⟶ H.obj (op (Q.obj Lc), Q.obj Mc) :=
    a.hom ≫ f ≫ H.map (b.hom.op, c.inv)
  let q := HomotopyCategory.quotient C (.up ℤ)
  let d := DerivedCategory.quotientCompQhIso.{wCD} C
  have hvSurj := (CochainComplex.IsKInjective.Qh_map_bijective
    (q.obj P) (homComplex (R := X.sheaf) Lc I)).surjective
      ((d.app P).hom ≫ g ≫ j.hom ≫ (d.app _).inv)
  rcases hvSurj with ⟨v, hv⟩
  have hφSurj := q.map_surjective v
  rcases hφSurj with ⟨φ, hφ⟩
  have hφQ : Q.map φ = g ≫ j.hom := by
    have hmap := (congrArg DerivedCategory.Qh.map hφ).trans hv
    have hn := (DerivedCategory.quotientCompQhIso_hom_naturality φ).symm.trans
      (congrArg (fun v ↦ v ≫ (d.app _).hom) hmap)
    change (d.app P).hom ≫ Q.map φ =
      ((d.app P).hom ≫ g ≫ j.hom ≫ (d.app (homComplex (R := X.sheaf) Lc I)).inv) ≫
        (d.app (homComplex (R := X.sheaf) Lc I)).hom at hn
    apply (cancel_epi (d.app P).hom).1
    simpa only [Category.assoc, Iso.inv_hom_id, Category.comp_id] using hn
  have hg : Q.map φ ≫ j.inv = g := by
    exact (congrArg (fun t ↦ t ≫ j.inv) hφQ).trans
      (by simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id])
  have hrep := h.2 P Lc Mc hP φ
  rcases hrep with ⟨ψ, hψ, he⟩
  have hrep' := h'.2 P Lc Mc hP φ
  rcases hrep' with ⟨ψ', hψ', he'⟩
  have eqψ : ψ = ψ' := by
    have := SheafOfModules.isMonoidal_W X.sheaf
    let := SheafOfModules.monoidalCategory X.sheaf
    let := SheafOfModules.symmetricCategory X.sheaf
    let := SheafOfModules.preservesZeroMorphisms_curriedTensor X.sheaf
    let := SheafOfModules.preservesZeroMorphisms_curriedTensor_obj X.sheaf
    have : Limits.HasColimitsOfSize.{0, 0} C :=
      Limits.hasColimitsOfSizeShrink.{0, 0, uCD, uCD} C
    apply HomologicalComplex.hom_ext
    intro n
    apply HomologicalComplex.mapBifunctor.hom_ext
      (K₁ := P) (K₂ := Lc) (F := curriedTensor C) (c := .up ℤ)
    intro p q hpq
    change p + q = n at hpq
    exact (hψ p q n hpq (by omega)).trans (hψ' p q n hpq (by omega)).symm
  have heq := he.trans ((congrArg (fun t ↦ pullbackTensorModelMap X P Lc ≫
    DerivedCategory.Q.map t ≫ schemeHomResolutionInverse X Mc) eqψ).trans he'.symm)
  change e (Q.obj P) (Q.obj Lc) (Q.obj Mc) (Q.map φ ≫ j.inv) =
    e' (Q.obj P) (Q.obj Lc) (Q.obj Mc) (Q.map φ ≫ j.inv) at heq
  have heqg := (congrArg (e (Q.obj P) (Q.obj Lc) (Q.obj Mc)) hg.symm).trans
    (heq.trans (congrArg (e' (Q.obj P) (Q.obj Lc) (Q.obj Mc)) hg))
  have hn := h.1 K (Q.obj P) L (Q.obj Lc) M (Q.obj Mc) a.hom b.hom c.inv f
  have hn' := h'.1 K (Q.obj P) L (Q.obj Lc) M (Q.obj Mc) a.hom b.hom c.inv f
  change e (Q.obj P) (Q.obj Lc) (Q.obj Mc) g = _ at hn
  change e' (Q.obj P) (Q.obj Lc) (Q.obj Mc) g = _ at hn'
  have heq' := hn.symm.trans (heqg.trans hn')
  have : IsIso (a.hom ⊗ₘ b.hom) := inferInstance
  exact (cancel_epi (a.hom ⊗ₘ b.hom)).1 ((cancel_mono c.inv).1
    (by simpa only [← Category.assoc] using heq'))

/-- Canonical family fixed by the representative equation.
Source: Stacks, cohomology.tex, Tag 08DJ
(blueprint: def-pc-canonical-derived-tensor-hom-bijection). -/
def schemeDerivedTensorHomEquiv (X : Scheme.{uCD})
    [HasDerivedCategory.{wCD} (SheafOfModules.{uCD} (moduleRings X.toRingedSpace))] :
    ∀ K L M : schemeDerivedCategory X,
      (K ⟶ (derivedInternalHom (Opens.grothendieckTopology X.toRingedSpace)
        X.toRingedSpace.sheaf).obj (op L, M)) ≃ (K ⊗ L ⟶ M) :=
  Classical.choose (exists_canonicalDerivedTensorHom X)

end AlgebraicGeometry
