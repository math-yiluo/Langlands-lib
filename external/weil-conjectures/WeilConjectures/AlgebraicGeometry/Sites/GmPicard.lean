/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Modules.TensorSection
public import WeilConjectures.AlgebraicGeometry.Modules.ProjectionFormula
public import WeilConjectures.AlgebraicGeometry.Picard.Group
public import WeilConjectures.AlgebraicGeometry.Sites.EtalePicard
public import WeilConjectures.AlgebraicGeometry.Sites.EtalePicardMul
public import WeilConjectures.AlgebraicGeometry.Sites.GmTorsorDescent
public import WeilConjectures.AlgebraicGeometry.Sites.Gm
public import WeilConjectures.AlgebraicGeometry.Sites.UnitsTorsor

/-!
# The Picard group as first étale cohomology of `𝔾ₘ`

For a scheme `X` the isomorphism classes of invertible `𝒪_X`-modules, the Zariski cohomology
`H¹(X_Zar, 𝒪_Xˣ)` and the étale cohomology `H¹(X_ét, 𝔾ₘ)` are in bijection (Hilbert 90).
All three classify torsors: an invertible module `L` gives the `𝔾ₘ`-torsor `Isom(𝒪, L)`, and
`H¹` of an abelian sheaf classifies its torsors.

## Main statements

- `AlgebraicGeometry.Scheme.picEquivQuotientTorsorGmSheaf`: the canonical bijection
  `L ↦ Isom(𝒪_X, L)` between invertible modules up to isomorphism and `𝔾ₘ`-torsors on `X_ét`
  (`AlgebraicGeometry.Scheme.Pic.etaleTorsorClass`). It is injective by
  `AlgebraicGeometry.Scheme.Pic.injective_etaleTorsorClass` and surjective by fpqc descent of
  invertible modules, `AlgebraicGeometry.Scheme.Pic.surjective_etaleTorsorClass`.
- `AlgebraicGeometry.Scheme.nonempty_equiv_quotient_torsor`: invertible modules up to
  isomorphism are in bijection with `𝔾ₘ`-torsors on `X_ét` and with `𝒪_Xˣ`-torsors on `X_Zar`.
- `AlgebraicGeometry.Scheme.Pic.toH1Units` and `AlgebraicGeometry.Scheme.Pic.toH1UnitsAddEquiv`:
  the canonical isomorphism of groups `Pic(X) ≃+ H¹(X_Zar, 𝒪_Xˣ)`, `L ↦ [Isom(𝒪_X, L)]`
  (additivity: `AlgebraicGeometry.Scheme.Pic.toH1Units_mul`).
- `AlgebraicGeometry.Scheme.Pic.toCohomologicalPicardGroup` and
  `AlgebraicGeometry.Scheme.Pic.toCohomologicalPicardGroupAddEquiv`: the canonical isomorphism
  `Pic(X) ≃+ H¹(X_ét, 𝔾ₘ)`, `L ↦ [Isom(𝒪_X, L)]`.
- `AlgebraicGeometry.Scheme.nonempty_equiv_H_one_unitsSheaf`: Hilbert 90,
  `Pic(X) ≃ H¹(X_Zar, 𝒪_Xˣ) ≃ H¹(X_ét, 𝔾ₘ)`.
- `AlgebraicGeometry.Scheme.nonempty_equiv_cohomologicalPicardGroup`,
  `AlgebraicGeometry.Scheme.nonempty_addEquiv_cohomologicalPicardGroup`: `Pic(X) ≃ H¹(X_ét, 𝔾ₘ)`,
  as sets and as groups.
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme

variable (X : Scheme.{u})

/-- **Every `𝔾ₘ`-torsor is `Isom(𝒪_X, L)`.** Every `𝔾ₘ`-torsor on the small étale site of `X`
is isomorphic to the torsor `Isom(𝒪_X, L)` of trivialisations of an invertible module `L`. -/
theorem Pic.surjective_etaleTorsorClass :
    Function.Surjective (Pic.etaleTorsorClass (X := X)) := by
  rintro ⟨T⟩
  obtain ⟨L, hL, h⟩ := Torsor.exists_etaleIsoTorsor_equiv T
  exact ⟨Pic.mk (L : X.Modules), (Pic.etaleTorsorClass_mk _).trans (Quotient.sound h)⟩

/-- **Line bundles and `𝔾ₘ`-torsors, étale version.** The canonical bijection `L ↦ Isom(𝒪_X, L)`
(`AlgebraicGeometry.Scheme.Pic.etaleTorsorClass`) from the Picard group of `X` onto the
isomorphism classes of `𝔾ₘ`-torsors on the small étale site of `X`. -/
noncomputable def picEquivQuotientTorsorGmSheaf :
    X.Pic ≃ _root_.Quotient (Sheaf.Torsor.setoid (G := X.gmSheaf)) :=
  Equiv.ofBijective _ ⟨Pic.injective_etaleTorsorClass, Pic.surjective_etaleTorsorClass X⟩

@[simp]
lemma picEquivQuotientTorsorGmSheaf_apply (L : X.Pic) :
    X.picEquivQuotientTorsorGmSheaf L = L.etaleTorsorClass :=
  rfl

/-- **Line bundles and `𝔾ₘ`-torsors, étale version.** For a scheme `X`, the isomorphism classes
of invertible `𝒪_X`-modules are in bijection with the isomorphism classes of `𝔾ₘ`-torsors on
the small étale site of `X`, by the canonical bijection
`AlgebraicGeometry.Scheme.picEquivQuotientTorsorGmSheaf`, `L ↦ Isom(𝒪_X, L)`. -/
theorem nonempty_pic_equiv_quotient_torsor_gmSheaf :
    Nonempty (X.Pic ≃ _root_.Quotient (Sheaf.Torsor.setoid (G := X.gmSheaf))) :=
  ⟨X.picEquivQuotientTorsorGmSheaf⟩

/-- **Line bundles and `𝔾ₘ`-torsors.** For a scheme `X`, the isomorphism classes of invertible
`𝒪_X`-modules are in bijection with the isomorphism classes of `𝔾ₘ`-torsors on the small étale
site of `X`, and with the isomorphism classes of `𝒪_Xˣ`-torsors on the Zariski site. The
canonical bijections send `L` to the torsor `Isom(𝒪, L)`. -/
theorem nonempty_equiv_quotient_torsor :
    Nonempty (X.Pic ≃ _root_.Quotient (Sheaf.Torsor.setoid (G := X.gmSheaf))) ∧
      Nonempty (X.Pic ≃ _root_.Quotient (Sheaf.Torsor.setoid (G := X.unitsSheaf))) :=
  ⟨X.nonempty_pic_equiv_quotient_torsor_gmSheaf, X.nonempty_pic_equiv_quotient_torsor_unitsSheaf⟩

/-- **The Picard group as Zariski cohomology of units.** The canonical bijection
`Pic(X) ≃ H¹(X_Zar, 𝒪_Xˣ)`, sending the class of an invertible module `L` to the class
(`CategoryTheory.Sheaf.Torsor.classH1`) of the `𝒪_Xˣ`-torsor `Isom(𝒪_X, L)` of local
generators of `L`. -/
noncomputable def Pic.toH1Units : X.Pic ≃ Sheaf.H X.unitsSheaf 1 :=
  X.picEquivQuotientTorsorUnitsSheaf.trans
    (Sheaf.Torsor.classH1 X.unitsSheaf (Limits.isTerminalTop (α := X.Opens)))

variable {X} in
/-- The class of an invertible module `M` in `H¹(X_Zar, 𝒪_Xˣ)` is the class of the torsor
`Isom(𝒪_X, M)` of its local generators. -/
lemma Pic.toH1Units_mk (M : X.Modules) [SheafOfModules.IsInvertible.{u, u, u} M] :
    Pic.toH1Units X (Pic.mk M) =
      Sheaf.Torsor.classH1 X.unitsSheaf (Limits.isTerminalTop (α := X.Opens))
        ⟦M.generatorsTorsor⟧ := by
  rw [Pic.toH1Units, Equiv.trans_apply, picEquivQuotientTorsorUnitsSheaf_apply,
    Pic.torsorClass_mk]

open MonoidalCategory in
/-- A tensor product of invertible modules is invertible, in the sense of
`SheafOfModules.IsInvertible`. -/
instance _root_.SheafOfModules.IsInvertible.tensorObj_scheme (M N : X.Modules)
    [SheafOfModules.IsInvertible.{u, u, u} M] [SheafOfModules.IsInvertible.{u, u, u} N] :
    SheafOfModules.IsInvertible.{u, u, u} (M ⊗ N : X.Modules) :=
  have := Modules.IsInvertible.of_sheafOfModules M
  have := Modules.IsInvertible.of_sheafOfModules N
  Modules.IsInvertible.sheafOfModules_isInvertible (M ⊗ N : X.Modules)

open Modules MonoidalCategory in
/-- The torsor of local generators of `M ⊗ N` has the class of the sum of the classes of the
torsors of generators of `M` and `N`. -/
lemma classH1_generatorsTorsor_tensorObj (M N : X.Modules)
    [SheafOfModules.IsInvertible.{u, u, u} M] [SheafOfModules.IsInvertible.{u, u, u} N] :
    Sheaf.Torsor.classH1 X.unitsSheaf (Limits.isTerminalTop (α := X.Opens))
        ⟦(M ⊗ N).generatorsTorsor⟧ =
      Sheaf.Torsor.classH1 X.unitsSheaf (Limits.isTerminalTop (α := X.Opens))
          ⟦M.generatorsTorsor⟧ +
        Sheaf.Torsor.classH1 X.unitsSheaf (Limits.isTerminalTop (α := X.Opens))
          ⟦N.generatorsTorsor⟧ := by
  refine Sheaf.Torsor.classH1_eq_add_of_equivariant _ _ _ _
    (fun U x x' ↦ ⟨tmulSection (show Γ(M, U.unop) from x.1) (show Γ(N, U.unop) from x'.1),
      IsFreeGenerator.tmulSection x.2 x'.2⟩) (fun U V f x x' ↦ Subtype.ext ?_)
    (fun U a x x' ↦ Subtype.ext (smul_tmulSection _ _ _))
    (fun U a x x' ↦ Subtype.ext (tmulSection_smul _ _ _))
  obtain ⟨⟨h⟩⟩ := f.unop
  exact tmulSection_map h _ _

/-- **`Pic(X) → H¹(X_Zar, 𝒪_Xˣ)` is additive**: the class of `L ⊗ L'` is the sum of the
classes. -/
lemma Pic.toH1Units_mul (L L' : X.Pic) :
    Pic.toH1Units X (L * L') = Pic.toH1Units X L + Pic.toH1Units X L' := by
  have h (L : X.Pic) : haveI := Pic.isInvertible L
      Pic.toH1Units X L =
        Sheaf.Torsor.classH1 X.unitsSheaf (Limits.isTerminalTop (α := X.Opens))
          ⟦((fromSkeleton X.Modules).obj L.val).generatorsTorsor⟧ := rfl
  have := Pic.isInvertible L
  have := Pic.isInvertible L'
  have := Pic.isInvertible (L * L')
  rw [h, h, h, _root_.Quotient.sound (Modules.generatorsTorsor_equiv_of_iso (Pic.mulIso L L')),
    classH1_generatorsTorsor_tensorObj]

/-- **The Picard group is the Zariski cohomology of units, as a group.** The canonical bijection
`AlgebraicGeometry.Scheme.Pic.toH1Units`, `L ↦ [Isom(𝒪_X, L)]`, as an isomorphism of groups
`Pic(X) ≃+ H¹(X_Zar, 𝒪_Xˣ)`. -/
noncomputable def Pic.toH1UnitsAddEquiv : Additive X.Pic ≃+ Sheaf.H X.unitsSheaf 1 where
  toEquiv := Additive.toMul.trans (Pic.toH1Units X)
  map_add' L L' := Pic.toH1Units_mul X L.toMul L'.toMul

/-- **The Picard group is `H¹(X, 𝔾ₘ)`, canonically.** The canonical bijection
`Pic(X) ≃ H¹(X_ét, 𝔾ₘ)` sending an invertible module `L` to the class
(`CategoryTheory.Sheaf.Torsor.classH1`) of the étale `𝔾ₘ`-torsor `Isom(𝒪_X, L)`. -/
noncomputable def Pic.toCohomologicalPicardGroup : X.Pic ≃ X.CohomologicalPicardGroup :=
  X.picEquivQuotientTorsorGmSheaf.trans
    (Sheaf.Torsor.classH1 X.gmSheaf (MorphismProperty.Over.mkIdTerminal @AlgebraicGeometry.Etale X))

lemma Pic.toCohomologicalPicardGroup_apply (L : X.Pic) :
    Pic.toCohomologicalPicardGroup X L =
      Sheaf.Torsor.classH1 X.gmSheaf (MorphismProperty.Over.mkIdTerminal @AlgebraicGeometry.Etale X)
        L.etaleTorsorClass :=
  rfl

/-- **`Pic(X) → H¹(X_ét, 𝔾ₘ)` is additive**: the class of `Isom(𝒪_X, L ⊗ L')` is the sum of the
classes of `Isom(𝒪_X, L)` and `Isom(𝒪_X, L')`. -/
theorem Pic.toCohomologicalPicardGroup_mul (L L' : X.Pic) :
    Pic.toCohomologicalPicardGroup X (L * L') =
      Pic.toCohomologicalPicardGroup X L + Pic.toCohomologicalPicardGroup X L' := by
  have := Pic.isInvertible L
  have := Pic.isInvertible L'
  have := Pic.isInvertible (L * L')
  rw [Pic.toCohomologicalPicardGroup_apply, Pic.toCohomologicalPicardGroup_apply,
    Pic.toCohomologicalPicardGroup_apply]
  change Sheaf.Torsor.classH1 _ _ ⟦Modules.etaleIsoTorsor
      ((fromSkeleton X.Modules).obj (L * L').val)⟧ =
    Sheaf.Torsor.classH1 _ _ ⟦Modules.etaleIsoTorsor ((fromSkeleton X.Modules).obj L.val)⟧ +
      Sheaf.Torsor.classH1 _ _ ⟦Modules.etaleIsoTorsor ((fromSkeleton X.Modules).obj L'.val)⟧
  rw [_root_.Quotient.sound (Modules.etaleIsoTorsor_equiv_of_iso _ _ (Pic.mulIso L L'))]
  exact Modules.classH1_etaleIsoTorsor_tensorObj _ _ _

/-- **Hilbert 90 for a scheme.** For a scheme `X` there are bijections

`{invertible 𝒪_X-modules}/≅ ≃ H¹(X_Zar, 𝒪_Xˣ) ≃ H¹(X_ét, 𝔾ₘ)`,

both sending an invertible module `L` to the class of the torsor `Isom(𝒪_X, L)`. -/
theorem nonempty_equiv_H_one_unitsSheaf :
    Nonempty (X.Pic ≃ Sheaf.H X.unitsSheaf 1) ∧
      Nonempty (Sheaf.H X.unitsSheaf 1 ≃ X.CohomologicalPicardGroup) :=
  ⟨⟨Pic.toH1Units X⟩, ⟨(Pic.toH1Units X).symm.trans (Pic.toCohomologicalPicardGroup X)⟩⟩

/-- **The Picard group is `H¹(X, 𝔾ₘ)`.** For a scheme `X` the isomorphism classes of invertible
`𝒪_X`-modules are in bijection with the cohomological Picard group `H¹(X_ét, 𝔾ₘ)`, by the
canonical bijection `AlgebraicGeometry.Scheme.Pic.toCohomologicalPicardGroup`,
`L ↦ [Isom(𝒪_X, L)]`. -/
theorem nonempty_equiv_cohomologicalPicardGroup :
    Nonempty (X.Pic ≃ X.CohomologicalPicardGroup) :=
  ⟨Pic.toCohomologicalPicardGroup X⟩

/-- **The Picard group is `H¹(X, 𝔾ₘ)` as a group.** The canonical bijection
`AlgebraicGeometry.Scheme.Pic.toCohomologicalPicardGroup`, `L ↦ [Isom(𝒪_X, L)]`, as an
isomorphism of groups `Pic(X) ≃+ H¹(X_ét, 𝔾ₘ)`. -/
noncomputable def Pic.toCohomologicalPicardGroupAddEquiv :
    Additive X.Pic ≃+ X.CohomologicalPicardGroup where
  toEquiv := Additive.toMul.trans (Pic.toCohomologicalPicardGroup X)
  map_add' L L' := Pic.toCohomologicalPicardGroup_mul X L.toMul L'.toMul

/-- **The Picard group is `H¹(X, 𝔾ₘ)` as a group.** For a scheme `X` the group `Pic(X)` of
invertible `𝒪_X`-modules up to isomorphism, under tensor product, is isomorphic to the
cohomological Picard group `H¹(X_ét, 𝔾ₘ)`, by the canonical isomorphism
`AlgebraicGeometry.Scheme.Pic.toCohomologicalPicardGroupAddEquiv`. -/
theorem nonempty_addEquiv_cohomologicalPicardGroup :
    Nonempty (Additive X.Pic ≃+ X.CohomologicalPicardGroup) :=
  ⟨Pic.toCohomologicalPicardGroupAddEquiv X⟩

end AlgebraicGeometry.Scheme
