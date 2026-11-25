/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.CanonicalPullbackTensorComparison
public import WeilConjectures.Algebra.Homology.HomTensorDegreewise
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.MonoidalClosed
import WeilConjectures.AlgebraicGeometry.NormalizedTensorHomCochainComponents

/-! # Component-normalized tensor-Hom equivalence on homotopy classes
Source: Stacks Project, Cohomology on Sites, Tag 0A90.
(blueprint: lem-pc-normalized-homotopy-tensor-hom).
-/

@[expose] public section

set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory CategoryTheory.MonoidalCategory Opposite TopologicalSpace
namespace AlgebraicGeometry

/-- Uncurrying induces a bijection on homotopy classes, with the actual component formula.
Source: Stacks Project, sites-cohomology.tex, Tag 0A90 (lemma-compose).
(blueprint: lem-pc-normalized-homotopy-tensor-hom).

Proof: use the degreewise isomorphisms `homTensorDegreewiseMap_spec` between the
iterated sheaf Hom complex and the Hom complex from the total tensor. Their
compatibility with differentials (`homTensorDegreewiseMap_comm`) makes them an
isomorphism of complexes. Construct the global-cochain comparisons on both sides
as in the proof of `homComplex_global_cochains`: use the product projections
specified by `Classical.choose_spec (homComplex_exists (R := X.sheaf))`
(the product specification exposed by `homComplex_projections_exists`), then
the internal-Hom sections equivalence on each factor. In particular, the component
of the comparison applied to s is
the morphism corresponding to s followed by the chosen product projection.
This component formula is needed; an arbitrary witness of the existential
statement `homComplex_global_cochains` does not supply normalization. The
product universal property gives the inverse comparison, and the differential
projection formula shows that these additive equivalences preserve the external
cochain differential. Hence they carry degree-zero cocycles to cocycles and degree-minus-one
boundaries to boundaries, in both directions. Chain maps are degree-zero cocycles;
the relation of differing by such a boundary is exactly chain homotopy. Passing
to these quotients therefore gives the displayed equivalence. For a chain map φ,
its image cocycle gives ψ. The degreewise pure-tensor specification says that the
restriction of ψ to P^p tensor L^q evaluates φ^p at the Hom projection indexed by
q and q+p. The sheaf tensor-Hom adjunction, preceded by symmetry, is exactly
the displayed uncurrying morphism. Equality before sheafification follows on pure
tensors; the tensor and sheafification universal properties imply the displayed
sheaf-morphism equation. This proves the normalization for every representative.
No flatness or injectivity is needed. If one input is zero both Hom sets are
singletons; unbounded inputs cause no difficulty because Hom uses products and
the total tensor uses coproducts. -/
theorem exists_normalizedHomotopyTensorHom (X : Scheme.{u})
    (P L I : CochainComplex (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ) :
    letI := SheafOfModules.monoidalCategory X.sheaf
    letI := SheafOfModules.symmetricCategory X.sheaf
    let q := HomotopyCategory.quotient
      (SheafOfModules.{u} (moduleRings X.toRingedSpace)) (.up ℤ)
    ∃ e : (q.obj P ⟶ q.obj (homComplex (R := X.sheaf) L I)) ≃
        (q.obj (pullbackTensorTotal X P L) ⟶ q.obj I),
      ∀ φ : P ⟶ homComplex (R := X.sheaf) L I,
        ∃ ψ : pullbackTensorTotal X P L ⟶ I,
          (∀ (p r n : ℤ) (h : p + r = n) (h' : r + p = n),
            HomologicalComplex.ιMapBifunctor P L (curriedTensor _) (.up ℤ) p r n h ≫
              ψ.f n =
              (β_ (P.X p) (L.X r)).hom ≫
                (SheafOfModules.tensorHomEquiv (L.X r) (P.X p) (I.X n)).symm
                  (φ.f p ≫ homTensorProjection X.sheaf L I p r n h')) ∧
          e (q.map φ) = q.map ψ := by
  classical
  let := SheafOfModules.monoidalCategory X.sheaf
  let := SheafOfModules.symmetricCategory X.sheaf
  let q := HomotopyCategory.quotient
    (SheafOfModules.{u} (moduleRings X.toRingedSpace)) (.up ℤ)
  let H := homComplex (R := X.sheaf) L I
  let T := pullbackTensorTotal X P L
  let a := normalizedTensorHomCochains X P L I
  have ha := normalizedTensorHomCochains_comm X P L I
  have hn := normalizedTensorHomCochains_component X P L I
  have hai (k m : ℤ) (c : CochainComplex.HomComplex.Cochain T I k) :
      (a m).symm (CochainComplex.HomComplex.δ k m c) =
        CochainComplex.HomComplex.δ k m ((a k).symm c) := by
    apply (a m).injective
    rw [AddEquiv.apply_symm_apply, ha, AddEquiv.apply_symm_apply]
  let ac : CochainComplex.HomComplex.Cocycle P H 0 ≃
      CochainComplex.HomComplex.Cocycle T I 0 :=
    { toFun z := CochainComplex.HomComplex.Cocycle.mk (a 0 z) 1 rfl (by
        rw [← ha, CochainComplex.HomComplex.Cocycle.δ_eq_zero]
        exact (a 1).map_zero)
      invFun z := CochainComplex.HomComplex.Cocycle.mk ((a 0).symm z) 1 rfl (by
        rw [← hai, CochainComplex.HomComplex.Cocycle.δ_eq_zero]
        exact (a 1).symm.map_zero)
      left_inv z := Subtype.ext ((a 0).symm_apply_apply z)
      right_inv z := Subtype.ext ((a 0).apply_symm_apply z) }
  let c : (P ⟶ H) ≃ (T ⟶ I) :=
    (CochainComplex.HomComplex.Cocycle.equivHom P H).toEquiv.trans
      (ac.trans (CochainComplex.HomComplex.Cocycle.equivHom T I).symm.toEquiv)
  have hc (φ : P ⟶ H) : CochainComplex.HomComplex.Cochain.ofHom (c φ) =
      a 0 (CochainComplex.HomComplex.Cochain.ofHom φ) := by
    exact CochainComplex.HomComplex.Cocycle.cochain_ofHom_homOf_eq_coe _
  have hhom (φ φ' : P ⟶ H) :
      Nonempty (Homotopy φ φ') ↔ Nonempty (Homotopy (c φ) (c φ')) := by
    constructor
    · rintro ⟨h⟩
      obtain ⟨z, hz⟩ := CochainComplex.HomComplex.Cochain.equivHomotopy φ φ' h
      refine ⟨(CochainComplex.HomComplex.Cochain.equivHomotopy (c φ) (c φ')).symm
        ⟨a (-1) z, ?_⟩⟩
      rw [hc, hc, ← ha, ← map_add, ← hz]
    · rintro ⟨h⟩
      obtain ⟨z, hz⟩ := CochainComplex.HomComplex.Cochain.equivHomotopy (c φ) (c φ') h
      refine ⟨(CochainComplex.HomComplex.Cochain.equivHomotopy φ φ').symm
        ⟨(a (-1)).symm z, ?_⟩⟩
      apply (a 0).injective
      rw [map_add, ha, AddEquiv.apply_symm_apply, ← hc, ← hc]
      exact hz
  have hmap (φ φ' : P ⟶ H) (h : q.map φ = q.map φ') :
      q.map (c φ) = q.map (c φ') := by
    exact HomotopyCategory.eq_of_homotopy _ _
      ((hhom φ φ').mp ⟨HomotopyCategory.homotopyOfEq _ _ h⟩).some
  have hmapi (ψ ψ' : T ⟶ I) (h : q.map ψ = q.map ψ') :
      q.map (c.symm ψ) = q.map (c.symm ψ') := by
    apply HomotopyCategory.eq_of_homotopy
    apply Nonempty.some
    apply (hhom (c.symm ψ) (c.symm ψ')).mpr
    simpa only [Equiv.apply_symm_apply] using
      (show Nonempty (Homotopy ψ ψ') from ⟨HomotopyCategory.homotopyOfEq _ _ h⟩)
  let f : (q.obj P ⟶ q.obj H) → (q.obj T ⟶ q.obj I) :=
    fun x ↦ q.map (c x.out)
  let g : (q.obj T ⟶ q.obj I) → (q.obj P ⟶ q.obj H) :=
    fun y ↦ q.map (c.symm y.out)
  have hf (φ : P ⟶ H) : f (q.map φ) = q.map (c φ) := by
    exact hmap _ _ (HomotopyCategory.quotient_map_out (q.map φ))
  have hg (ψ : T ⟶ I) : g (q.map ψ) = q.map (c.symm ψ) := by
    exact hmapi _ _ (HomotopyCategory.quotient_map_out (q.map ψ))
  let e : (q.obj P ⟶ q.obj H) ≃ (q.obj T ⟶ q.obj I) :=
    { toFun := f
      invFun := g
      left_inv x := by
        change g (q.map (c x.out)) = x
        rw [hg, Equiv.symm_apply_apply]
        exact HomotopyCategory.quotient_map_out x
      right_inv y := by
        change f (q.map (c.symm y.out)) = y
        rw [hf, Equiv.apply_symm_apply]
        exact HomotopyCategory.quotient_map_out y }
  refine ⟨e, fun φ ↦ ⟨c φ, ?_, hf φ⟩⟩
  intro p r n h h'
  have hn' := hn (CochainComplex.HomComplex.Cochain.ofHom φ) p r n h h'
  rw [← hc, CochainComplex.HomComplex.Cochain.ofHom_v,
    CochainComplex.HomComplex.Cochain.ofHom_v] at hn'
  exact hn'

end AlgebraicGeometry
