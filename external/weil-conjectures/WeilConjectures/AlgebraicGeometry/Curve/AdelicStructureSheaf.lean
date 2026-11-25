/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Curve.AdelicH1
public import WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.AffineMorphism

/-!
# The local rings of a curve inside its function field

Let `X` be an integral scheme over a field `k`, with function field `K`. For a point `x` the
local ring `𝒪_{X,x}` is the subring `AlgebraicGeometry.Scheme.localSubalgebra k X x` of `K` of
germs at the generic point of the functions regular near `x`. The inclusion
`𝒪_X ⟶ K_η` of the structure sheaf into the constant sheaf `K` is injective on sections and every
element of `K` is regular on some nonempty open, so the residue sequence of
`AlgebraicGeometry.Scheme.Modules.adelicH1Equiv` applies to `𝒪_X`:
```
  H¹(X, 𝒪_X) ≅ (⨁_{x closed} K ⧸ 𝒪_{X,x}) ⧸ K,      H⁰(X, 𝒪_X) ≅ ⋂_{x closed} 𝒪_{X,x}.
```
For `X` proper over `k` both are finite-dimensional.

## Main definitions

- `AlgebraicGeometry.Scheme.functionFieldAlgebra`: the `k`-algebra structure of `K`.
- `AlgebraicGeometry.Scheme.Modules.structureSheafToGeneric`: the inclusion `𝒪_X ⟶ K_η`.
- `AlgebraicGeometry.Scheme.localSubalgebra`: the local ring `𝒪_{X,x} ⊆ K` as a `k`-subalgebra.

## Main statements

- `AlgebraicGeometry.Scheme.finite_setOf_not_mem_localSubalgebra`: every `f ∈ K` lies in
  `𝒪_{X,x}` for all but finitely many closed points `x`.
- `AlgebraicGeometry.Scheme.structureSheafH1Equiv`: `H¹(X, 𝒪_X) ≅ (⨁_x K ⧸ 𝒪_{X,x}) ⧸ K`.
- `AlgebraicGeometry.Scheme.finiteDimensional_iInf_localSubalgebra` and
  `AlgebraicGeometry.Scheme.finiteDimensional_quotient_range_localPrincipalPartsMap`:
  finiteness of `⋂_x 𝒪_{X,x}` and of `(⨁_x K ⧸ 𝒪_{X,x}) ⧸ K` for `X` proper.

(blueprint: `theorem-riemann-roch-coherent-serre-duality--2`)
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite TopologicalSpace

namespace AlgebraicGeometry.Scheme

variable (k : Type u) [Field k] (X : Scheme.{u}) [IsIntegral X] [X.Over (Spec (.of k))]

/-- The `k`-algebra structure on the function field of an integral `k`-scheme: the composite
`k → Γ(X, 𝒪_X) → K` of the structure map and the germ at the generic point. -/
@[instance_reducible]
noncomputable def functionFieldAlgebra : Algebra k X.functionField :=
  ((X.presheaf.germ ⊤ (genericPoint X) trivial).hom.comp
    (globalSectionsRingHom k (X := X))).toAlgebra

lemma isFunctionFieldAlgebra_functionFieldAlgebra :
    letI := functionFieldAlgebra k X
    IsFunctionFieldAlgebra k X :=
  letI := functionFieldAlgebra k X
  ⟨fun _ ↦ rfl⟩

namespace Modules

variable {X}

/-- The values `U ↦ (germ at η)` of the inclusion of the structure sheaf into the constant
sheaf `K`. -/
noncomputable def structureSheafToGenericPresheafHom :
    Modules.presheaf (SheafOfModules.unit X.ringCatSheaf) ⟶
      (skyscraper (genericPoint X) X.functionField).presheaf where
  app U := AddCommGrpCat.ofHom
    { toFun a := show SkyscraperSections (genericPoint X) X.functionField U.unop from
        fun h ↦ X.presheaf.germ U.unop _ h.down a
      map_zero' := SkyscraperSections.ext fun _ ↦ map_zero (X.presheaf.germ U.unop _ _).hom
      map_add' a b := SkyscraperSections.ext fun _ ↦
        map_add (X.presheaf.germ U.unop _ _).hom a b }
  naturality U U' i := by
    ext a
    refine SkyscraperSections.ext fun h ↦ ?_
    exact X.presheaf.germ_res_apply i.unop _ _ a

variable (X) in
/-- The inclusion `𝒪_X ⟶ K_η` of the structure sheaf into the constant sheaf with value the
function field, given by the germs at the generic point. -/
noncomputable def structureSheafToGeneric :
    SheafOfModules.unit X.ringCatSheaf ⟶ skyscraper (genericPoint X) X.functionField :=
  ⟨PresheafOfModules.homMk structureSheafToGenericPresheafHom fun U r a ↦
    SkyscraperSections.ext fun h ↦ map_mul (X.presheaf.germ U.unop _ h).hom r a⟩

@[simp]
lemma genericValue_structureSheafToGeneric {U : X.Opens} (h : genericPoint X ∈ U)
    (a : Γ(X, U)) :
    genericValue (structureSheafToGeneric X) h a = X.presheaf.germ U _ h a :=
  rfl

/-- The inclusion `𝒪_X ⟶ K_η` is injective on sections. -/
lemma injective_structureSheafToGeneric_app (U : X.Opens) :
    Function.Injective (Hom.app (structureSheafToGeneric X) U) := by
  by_cases hU : genericPoint X ∈ U
  · intro a b h
    refine germ_injective_of_isIntegral X _ hU ?_
    exact congr_arg (fun t : SkyscraperSections (genericPoint X) X.functionField U ↦ t ⟨hU⟩) h
  · have : U = ⊥ := eq_bot_iff.2 fun x hx ↦ hU (genericPoint_mem_of_mem hx)
    subst this
    intro a b _
    exact Subsingleton.elim (α := Γ(X, ⊥)) a b

variable [Algebra k X.functionField] [IsFunctionFieldAlgebra k X]

/-- Every element of the function field is the germ of a function on a nonempty open. -/
lemma mem_stalkLattice_structureSheafToGeneric_genericPoint (f : X.functionField) :
    f ∈ stalkLattice k (structureSheafToGeneric X) (genericPoint X) := by
  obtain ⟨U, hU, a, rfl⟩ := X.presheaf.exists_germ_eq f
  exact ⟨U, hU, a, rfl⟩

end Modules

variable [Algebra k X.functionField] [IsFunctionFieldAlgebra k X]

/-- The **local ring** `𝒪_{X,x}` of an integral `k`-scheme at a point `x`, as the `k`-subalgebra
of the function field `K` of germs at the generic point of the functions regular near `x`. -/
noncomputable def localSubalgebra (x : X) : Subalgebra k X.functionField where
  carrier := Modules.stalkLattice k (Modules.structureSheafToGeneric X) x
  mul_mem' := by
    rintro _ _ ⟨U, hU, a, rfl⟩ ⟨U', hU', b, rfl⟩
    refine ⟨U ⊓ U', ⟨hU, hU'⟩, X.presheaf.map (homOfLE (inf_le_left : U ⊓ U' ≤ U)).op a *
      X.presheaf.map (homOfLE (inf_le_right : U ⊓ U' ≤ U')).op b, ?_⟩
    simp only [Modules.genericValue_structureSheafToGeneric, map_mul,
      X.presheaf.germ_res_apply]
  add_mem' := (Modules.stalkLattice k (Modules.structureSheafToGeneric X) x).add_mem
  algebraMap_mem' c := by
    rw [IsFunctionFieldAlgebra.algebraMap_eq]
    exact ⟨⊤, trivial, globalSectionsRingHom k (X := X) c, rfl⟩

lemma localSubalgebra_toSubmodule (x : X) :
    Subalgebra.toSubmodule (localSubalgebra k X x) =
      Modules.stalkLattice k (Modules.structureSheafToGeneric X) x :=
  rfl

lemma mem_localSubalgebra {x : X} {f : X.functionField} :
    f ∈ localSubalgebra k X x ↔
      ∃ (U : X.Opens) (hx : x ∈ U) (a : Γ(X, U)),
        X.presheaf.germ U _ (genericPoint_mem_of_mem hx) a = f :=
  Iff.rfl

/-- The local subalgebra `𝒪_{X,x} ⊆ K` is the image of the stalk `𝒪_{X,x} → K`. -/
lemma coe_localSubalgebra (x : X) :
    (localSubalgebra k X x : Set X.functionField) =
      Set.range (algebraMap (X.presheaf.stalk x) X.functionField) := by
  ext f
  constructor
  · rintro ⟨U, hU, a, rfl⟩
    refine ⟨X.presheaf.germ U x hU a, ?_⟩
    have : Nonempty U := ⟨⟨x, hU⟩⟩
    exact Scheme.algebraMap_germ_eq_germToFunctionField X hU a
  · rintro ⟨g, rfl⟩
    obtain ⟨U, hU, a, rfl⟩ := X.presheaf.exists_germ_eq g
    have : Nonempty U := ⟨⟨x, hU⟩⟩
    exact ⟨U, hU, a, (Scheme.algebraMap_germ_eq_germToFunctionField X hU a).symm⟩

/-- The stalk `𝒪_{X,x}` is isomorphic to the local subalgebra `𝒪_{X,x} ⊆ K`. -/
noncomputable def stalkEquivLocalSubalgebra (x : X) :
    X.presheaf.stalk x ≃+* localSubalgebra k X x :=
  RingEquiv.ofBijective
    ((algebraMap (X.presheaf.stalk x) X.functionField).codRestrict
      (localSubalgebra k X x).toSubsemiring fun g ↦ by
        change _ ∈ (localSubalgebra k X x : Set X.functionField)
        rw [coe_localSubalgebra]
        exact ⟨g, rfl⟩)
    ⟨fun g g' h ↦ by
      have h' := congr_arg Subtype.val h
      obtain ⟨U, hU, a, rfl⟩ := X.presheaf.exists_germ_eq g
      obtain ⟨U', hU', a', rfl⟩ := X.presheaf.exists_germ_eq g'
      have hx : x ∈ U ⊓ U' := ⟨hU, hU'⟩
      rw [← X.presheaf.germ_res_apply (homOfLE inf_le_left : U ⊓ U' ⟶ U) x hx a,
        ← X.presheaf.germ_res_apply (homOfLE inf_le_right : U ⊓ U' ⟶ U') x hx a'] at h' ⊢
      have : Nonempty (U ⊓ U' : X.Opens) := ⟨⟨x, hx⟩⟩
      change algebraMap _ _ _ = algebraMap _ _ _ at h'
      rw [Scheme.algebraMap_germ_eq_germToFunctionField X hx,
        Scheme.algebraMap_germ_eq_germToFunctionField X hx] at h'
      rw [Scheme.germToFunctionField_injective X _ h'],
    fun f ↦ by
      obtain ⟨g, hg⟩ : (f : X.functionField) ∈ Set.range
          (algebraMap (X.presheaf.stalk x) X.functionField) := by
        rw [← coe_localSubalgebra k]
        exact f.2
      exact ⟨g, Subtype.ext hg⟩⟩

@[simp]
lemma coe_stalkEquivLocalSubalgebra (x : X) (g : X.presheaf.stalk x) :
    (stalkEquivLocalSubalgebra k X x g : X.functionField) =
      algebraMap (X.presheaf.stalk x) X.functionField g :=
  rfl

section Curve

variable [NoetherianSpace X] (hdim : topologicalKrullDim X ≤ 1)

include hdim in
/-- Every `f ∈ K` lies in `𝒪_{X,x}` for all but finitely many closed points `x`. -/
theorem finite_setOf_not_mem_localSubalgebra (f : X.functionField) :
    {x : closedPoints X | f ∉ localSubalgebra k X x}.Finite :=
  (Modules.finite_setOf_not_mem_stalkLattice k _ hdim
    (Modules.mem_stalkLattice_structureSheafToGeneric_genericPoint k) f).preimage
      Subtype.val_injective.injOn |>.subset fun _ hx ↦ hx

/-- The principal parts map `K → ⨁_{x closed} K ⧸ 𝒪_{X,x}`. -/
noncomputable def localPrincipalPartsMap :
    X.functionField →ₗ[k]
      Π₀ x : closedPoints X,
        X.functionField ⧸ Modules.stalkLattice k (Modules.structureSheafToGeneric X) x.1 :=
  Modules.principalPartsMap k (Modules.structureSheafToGeneric X) hdim
    (Modules.mem_stalkLattice_structureSheafToGeneric_genericPoint k)

@[simp]
lemma localPrincipalPartsMap_apply (f : X.functionField) (x : closedPoints X) :
    localPrincipalPartsMap k X hdim f x = Submodule.Quotient.mk f :=
  rfl

/-- **`H¹(X, 𝒪_X)` via principal parts**: for an integral noetherian `k`-scheme of dimension at
most one, `H¹(X, 𝒪_X) ≅ (⨁_{x closed} K ⧸ 𝒪_{X,x}) ⧸ K`, canonically.

(blueprint: `theorem-riemann-roch-coherent-serre-duality--2`) -/
noncomputable def structureSheafH1Equiv :
    Modules.H (SheafOfModules.unit X.ringCatSheaf) 1 ≃ₗ[k]
      (Π₀ x : closedPoints X,
        X.functionField ⧸ Modules.stalkLattice k (Modules.structureSheafToGeneric X) x.1) ⧸
        LinearMap.range (localPrincipalPartsMap k X hdim) :=
  Modules.adelicH1Equiv k hdim (Modules.mem_stalkLattice_structureSheafToGeneric_genericPoint k)
    Modules.injective_structureSheafToGeneric_app

omit [NoetherianSpace X] in
/-- **`H⁰(X, 𝒪_X)` as an intersection of local rings**: `H⁰(X, 𝒪_X) ≅ ⋂_{x closed} 𝒪_{X,x}`. -/
noncomputable def structureSheafH0Equiv :
    Modules.H (SheafOfModules.unit X.ringCatSheaf) 0 ≃ₗ[k]
      ↥(⨅ x : closedPoints X, Modules.stalkLattice k (Modules.structureSheafToGeneric X) x.1) :=
  Modules.adelicH0Equiv k hdim (Modules.mem_stalkLattice_structureSheafToGeneric_genericPoint k)
    Modules.injective_structureSheafToGeneric_app

variable [IsProper (X ↘ Spec (.of k))]

include hdim in
omit [NoetherianSpace X] in
/-- On a proper integral curve, `⋂_{x closed} 𝒪_{X,x}` is finite-dimensional over `k`. -/
theorem finiteDimensional_iInf_localSubalgebra :
    FiniteDimensional k
      ↥(⨅ x : closedPoints X, Modules.stalkLattice k (Modules.structureSheafToGeneric X) x.1) := by
  have : (SheafOfModules.unit X.ringCatSheaf).IsFinitePresentation := by
    have : (SheafOfModules.unit X.ringCatSheaf).IsInvertible :=
      SheafOfModules.instIsInvertibleUnit.{u, u, u}
    have : (SheafOfModules.unit X.ringCatSheaf).IsFiniteLocallyFree :=
      SheafOfModules.IsInvertible.isFiniteLocallyFree.{u, u, u} _
    exact SheafOfModules.IsFiniteLocallyFree.isFinitePresentation.{u, u, u} _
  have := Modules.finiteDimensional_H_of_isProper (k := k) (SheafOfModules.unit X.ringCatSheaf) 0
  exact Module.Finite.equiv (structureSheafH0Equiv k X hdim)

/-- On a proper integral curve, the cokernel of `K → ⨁_{x closed} K ⧸ 𝒪_{X,x}` is
finite-dimensional over `k`: it is `H¹(X, 𝒪_X)`. -/
theorem finiteDimensional_quotient_range_localPrincipalPartsMap :
    FiniteDimensional k
      ((Π₀ x : closedPoints X,
        X.functionField ⧸ Modules.stalkLattice k (Modules.structureSheafToGeneric X) x.1) ⧸
        LinearMap.range (localPrincipalPartsMap k X hdim)) := by
  have : (SheafOfModules.unit X.ringCatSheaf).IsFinitePresentation := by
    have : (SheafOfModules.unit X.ringCatSheaf).IsInvertible :=
      SheafOfModules.instIsInvertibleUnit.{u, u, u}
    have : (SheafOfModules.unit X.ringCatSheaf).IsFiniteLocallyFree :=
      SheafOfModules.IsInvertible.isFiniteLocallyFree.{u, u, u} _
    exact SheafOfModules.IsFiniteLocallyFree.isFinitePresentation.{u, u, u} _
  have := Modules.finiteDimensional_H_of_isProper (k := k) (SheafOfModules.unit X.ringCatSheaf) 1
  exact Module.Finite.equiv (structureSheafH1Equiv k X hdim)

end Curve

end AlgebraicGeometry.Scheme
