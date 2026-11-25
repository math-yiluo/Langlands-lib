/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Curve.AdelicStructureSheaf
public import WeilConjectures.AlgebraicGeometry.Curve.SmoothSections
public import WeilConjectures.AlgebraicGeometry.Modules.DifferentialsSections

/-!
# The residue sequence of the sheaf of differentials of a curve

Let `X` be an integral scheme smooth over a field `k`, with function field `K`, and let
`ω = Ω¹_{X/k}`. The germs at the generic point of differentials define a morphism
`ω ⟶ Ω[K⁄k]_η` to the constant sheaf with value the Kähler differentials of `K`
(`AlgebraicGeometry.Scheme.differentialsToGeneric`), sending `a db` to `a db`. It is injective on
sections (on an affine open `U`, `Γ(U, ω) = Ω[Γ(X, U)⁄k]` is projective, hence torsion free, and
`Ω[K⁄k]` is its localization), every element of `Ω[K⁄k]` is a local section, and the subspace
`ω_x ⊆ Ω[K⁄k]` of germs of differentials regular at `x` is the image of `Ω[𝒪_{X,x}⁄k]`
(`AlgebraicGeometry.Scheme.coe_stalkLattice_differentialsToGeneric`).

So the residue sequence `0 ⟶ ω ⟶ Ω[K⁄k]_η ⟶ 𝒫 ⟶ 0` gives, for `X` of dimension one,
```
  H¹(X, ω) ≅ (⨁_{x closed} Ω[K⁄k] ⧸ ω_x) ⧸ Ω[K⁄k]
```
(`AlgebraicGeometry.Scheme.differentialsH1Equiv`).

(blueprint: `theorem-riemann-roch-coherent-serre-duality--2`)
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite TopologicalSpace

namespace AlgebraicGeometry.Scheme

variable (k : Type u) [Field k] (X : Scheme.{u}) [IsIntegral X] [X.Over (Spec (.of k))]
  [Algebra k X.functionField] [IsFunctionFieldAlgebra k X]

/-- The derivation `𝒪_X → Ω[K⁄k]_η`, `a ↦ d(germ a)`, relative to `k`. -/
noncomputable def genericDerivation :
    (Modules.skyscraper (genericPoint X) Ω[X.functionField⁄k]).val.Derivation'
      (X ↘ Spec (.of k)).pullbackPresheafToPresheaf :=
  Hom.derivationMk _
    (fun {U} ↦
      { toFun a := show Modules.SkyscraperSections (genericPoint X) Ω[X.functionField⁄k] U.unop from
          fun h ↦ KaehlerDifferential.D k X.functionField (X.presheaf.germ U.unop _ h.down a)
        map_zero' := Modules.SkyscraperSections.ext fun _ ↦ by
          change KaehlerDifferential.D k X.functionField (X.presheaf.germ _ _ _ 0) = 0
          rw [map_zero, map_zero]
        map_add' a b := Modules.SkyscraperSections.ext fun _ ↦ by
          change KaehlerDifferential.D k X.functionField (X.presheaf.germ _ _ _ (a + b)) =
            KaehlerDifferential.D k X.functionField (X.presheaf.germ _ _ _ a) +
              KaehlerDifferential.D k X.functionField (X.presheaf.germ _ _ _ b)
          rw [map_add, map_add] })
    (fun {U} a b ↦ Modules.SkyscraperSections.ext fun h ↦ by
      change KaehlerDifferential.D k X.functionField (X.presheaf.germ _ _ _ (a * b)) =
        X.presheaf.germ _ _ h a • KaehlerDifferential.D k X.functionField
          (X.presheaf.germ _ _ _ b) +
        X.presheaf.germ _ _ h b • KaehlerDifferential.D k X.functionField
          (X.presheaf.germ _ _ _ a)
      rw [map_mul, Derivation.leibniz])
    (fun {U U'} i a ↦ Modules.SkyscraperSections.ext fun h ↦ by
      change KaehlerDifferential.D k X.functionField
          (X.presheaf.germ _ _ _ (X.presheaf.map i a)) =
        KaehlerDifferential.D k X.functionField (X.presheaf.germ _ _ _ a)
      exact congrArg (KaehlerDifferential.D k X.functionField)
        (X.presheaf.germ_res_apply i.unop _ _ a))
    (fun V a ↦ Modules.SkyscraperSections.ext fun h ↦ by
      obtain rfl : V = ⊤ := eq_top_iff.2 fun y _ ↦
        Subsingleton.elim ((X ↘ Spec (.of k)) (genericPoint X)) y ▸ h
      change KaehlerDifferential.D k X.functionField
          (X.presheaf.germ ⊤ _ trivial ((X ↘ Spec (.of k)).appTop a)) = 0
      have : (X ↘ Spec (.of k)).appTop a =
          globalSectionsRingHom k (X := X) ((Scheme.ΓSpecIso (.of k)).hom a) := by
        simp [globalSectionsRingHom]
      rw [this, ← IsFunctionFieldAlgebra.algebraMap_eq, Derivation.map_algebraMap])

/-- The morphism `ω = Ω¹_{X/k} ⟶ Ω[K⁄k]_η` from the sheaf of differentials to the constant sheaf
with value the Kähler differentials of the function field, sending `a db` to
`germ(a) d(germ b)`. -/
noncomputable def differentialsToGeneric :
    (X ↘ Spec (.of k)).relativeDifferentials ⟶
      Modules.skyscraper (genericPoint X) Ω[X.functionField⁄k] :=
  ((X ↘ Spec (.of k)).relativeDifferentialsHomEquiv _).symm (genericDerivation k X)

variable {X} in
@[simp]
lemma genericValue_differentialsToGeneric_sectionsD {U : X.Opens} (h : genericPoint X ∈ U)
    (a : Γ(X, U)) :
    Modules.genericValue (differentialsToGeneric k X) h ((X ↘ Spec (.of k)).sectionsD U a) =
      KaehlerDifferential.D k X.functionField (X.presheaf.germ U _ h a) := by
  have := (X ↘ Spec (.of k)).relativeDifferentialsHomEquiv_symm_app_d (genericDerivation k X)
    (U := op U) a
  exact congr_arg
    (fun t : Modules.SkyscraperSections (genericPoint X) Ω[X.functionField⁄k] U ↦ t ⟨h⟩) this

/-- Every element of `Ω[K⁄k]` is the germ of a differential on a nonempty open. -/
lemma mem_stalkLattice_differentialsToGeneric_genericPoint (v : Ω[X.functionField⁄k]) :
    v ∈ Modules.stalkLattice k (differentialsToGeneric k X) (genericPoint X) := by
  have hspan := KaehlerDifferential.span_range_derivation k X.functionField
  have hv : v ∈ Submodule.span X.functionField
      (Set.range (KaehlerDifferential.D k X.functionField)) := hspan ▸ Submodule.mem_top
  induction hv using Submodule.span_induction with
  | mem w hw =>
    obtain ⟨g, rfl⟩ := hw
    obtain ⟨U, hU, a, rfl⟩ := X.presheaf.exists_germ_eq g
    exact ⟨U, hU, _, genericValue_differentialsToGeneric_sectionsD k hU a⟩
  | zero => exact Submodule.zero_mem _
  | add w w' _ _ hw hw' => exact Submodule.add_mem _ hw hw'
  | smul c w _ hw =>
    obtain ⟨U, hU, a, rfl⟩ := X.presheaf.exists_germ_eq c
    exact Modules.germ_smul_mem_stalkLattice _ hU a hw

variable {X}

/-- On an affine open `U` (with the structure map as `k`-algebra structure), the value in
`Ω[K⁄k]` of the section of `ω` corresponding to `a db ∈ Ω[Γ(X, U)⁄k]` is `germ(a) d(germ b)`; in
particular every such value is a `K`-combination of differentials of germs, by induction on
`Ω[Γ(X, U)⁄k] = span {db}`. -/
lemma genericValue_kaehlerSectionsEquiv_induction {U : X.Opens} (hU : IsAffineOpen U)
    (h : genericPoint X ∈ U) [Algebra k Γ(X, U)]
    (hA : algebraMap k Γ(X, U) = ((X ↘ Spec (.of k)).specStructureMap U).hom)
    (P : Ω[X.functionField⁄k] → Prop) (h0 : P 0) (hadd : ∀ v w, P v → P w → P (v + w))
    (hsmul : ∀ (a : Γ(X, U)) v, P v → P (X.presheaf.germ U _ h a • v))
    (hD : ∀ b : Γ(X, U), P (KaehlerDifferential.D k X.functionField (X.presheaf.germ U _ h b)))
    (ω : Ω[Γ(X, U)⁄k]) :
    P (Modules.genericValue (differentialsToGeneric k X) h
      ((X ↘ Spec (.of k)).kaehlerSectionsEquiv U hA hU ω)) := by
  have hω : ω ∈ Submodule.span Γ(X, U) (Set.range (KaehlerDifferential.D k Γ(X, U))) :=
    (KaehlerDifferential.span_range_derivation k Γ(X, U)).symm ▸ Submodule.mem_top
  induction hω using Submodule.span_induction with
  | mem w hw =>
    obtain ⟨b, rfl⟩ := hw
    rw [Hom.kaehlerSectionsEquiv_D, genericValue_differentialsToGeneric_sectionsD]
    exact hD b
  | zero => rw [map_zero, Modules.genericValue_zero]; exact h0
  | add w w' _ _ hw hw' => rw [map_add, Modules.genericValue_add]; exact hadd _ _ hw hw'
  | smul a w _ hw => rw [LinearEquiv.map_smul, Modules.genericValue_smul]; exact hsmul a _ hw

/-- On an affine open, the value map `Γ(U, ω) → Ω[K⁄k]` is injective: `Γ(U, ω) = Ω[Γ(X, U)⁄k]`
is projective (`Γ(X, U)` is smooth over `k`), hence torsion free, and `Ω[K⁄k]` is its
localization at the nonzero elements. -/
lemma injective_genericValue_differentialsToGeneric [Smooth (X ↘ Spec (.of k))] {U : X.Opens}
    (hU : IsAffineOpen U) (h : genericPoint X ∈ U) :
    Function.Injective (Modules.genericValue (differentialsToGeneric k X) h) := by
  have : Nonempty U := ⟨⟨_, h⟩⟩
  let := ((X ↘ Spec (.of k)).specStructureMap U).hom.toAlgebra
  have hA : algebraMap k Γ(X, U) = ((X ↘ Spec (.of k)).specStructureMap U).hom := rfl
  have : Algebra.Smooth k Γ(X, U) := smooth_sections hU hA
  have := functionField_isFractionRing_of_isAffineOpen X U hU
  have : IsScalarTower k Γ(X, U) X.functionField := by
    refine IsScalarTower.of_algebraMap_eq' (RingHom.ext fun c ↦ ?_)
    change algebraMap k X.functionField c = X.presheaf.germ U _ h
      (((Scheme.ΓSpecIso (.of k)).inv ≫ (X ↘ Spec (.of k)).appLE ⊤ U le_top) c)
    rw [IsFunctionFieldAlgebra.algebraMap_eq, Scheme.Hom.appLE, ← Category.assoc,
      CategoryTheory.comp_apply, X.presheaf.germ_res_apply]
    rfl
  let e := (X ↘ Spec (.of k)).kaehlerSectionsEquiv U hA hU
  have key (ω : Ω[Γ(X, U)⁄k]) : Modules.genericValue (differentialsToGeneric k X) h (e ω) =
      KaehlerDifferential.map k k Γ(X, U) X.functionField ω := by
    have hω : ω ∈ Submodule.span Γ(X, U) (Set.range (KaehlerDifferential.D k Γ(X, U))) :=
      (KaehlerDifferential.span_range_derivation k Γ(X, U)).symm ▸ Submodule.mem_top
    induction hω using Submodule.span_induction with
    | mem w hw =>
      obtain ⟨b, rfl⟩ := hw
      rw [Hom.kaehlerSectionsEquiv_D, genericValue_differentialsToGeneric_sectionsD,
        KaehlerDifferential.map_D]
      rfl
    | zero => rw [map_zero, Modules.genericValue_zero, map_zero]
    | add w w' _ _ hw hw' => rw [map_add, Modules.genericValue_add, map_add, hw, hw']
    | smul a w _ hw =>
      rw [LinearEquiv.map_smul, Modules.genericValue_smul, LinearMap.map_smul, hw,
        ← algebraMap_smul X.functionField a]
      rfl
  have hinj : Function.Injective (KaehlerDifferential.map k k Γ(X, U) X.functionField) := by
    refine (injective_iff_map_eq_zero _).2 fun w hw ↦ ?_
    obtain ⟨⟨r, hr⟩, hrw⟩ :=
      (IsLocalizedModule.eq_zero_iff (nonZeroDivisors Γ(X, U)) _).1 hw
    exact Module.Flat.isSMulRegular_of_nonZeroDivisors hr (by simpa using hrw)
  intro s t hst
  obtain ⟨ω, rfl⟩ := e.surjective s
  obtain ⟨ω', rfl⟩ := e.surjective t
  rw [key, key] at hst
  rw [hinj hst]

/-- The morphism `ω ⟶ Ω[K⁄k]_η` is injective on sections, for `X` smooth over `k`. -/
theorem injective_differentialsToGeneric_app [Smooth (X ↘ Spec (.of k))] (U : X.Opens) :
    Function.Injective (Modules.Hom.app (differentialsToGeneric k X) U) := by
  intro s t hst
  let F : TopCat.Sheaf Ab.{u} X := ⟨(X ↘ Spec (.of k)).relativeDifferentials.presheaf,
    Modules.isSheaf _⟩
  have hb (x : U) := (Opens.isBasis_iff_nbhd.1 X.isBasis_affineOpens) x.2
  choose W hW hxW hWU using hb
  refine F.eq_of_locally_eq' (U := W) U (fun x ↦ homOfLE (hWU x))
    (fun x hx ↦ Opens.mem_iSup.2 ⟨⟨x, hx⟩, hxW ⟨x, hx⟩⟩) s t fun x ↦ ?_
  have hη : genericPoint X ∈ W x := genericPoint_mem_of_mem (hxW x)
  refine injective_genericValue_differentialsToGeneric k (hW x) hη ?_
  change Modules.genericValue _ hη (_root_.AlgebraicGeometry.Scheme.Modules.presheaf _ |>.map
    (homOfLE (hWU x)).op s) = Modules.genericValue _ hη (Modules.presheaf _ |>.map
    (homOfLE (hWU x)).op t)
  rw [Modules.genericValue_res, Modules.genericValue_res]
  exact congr_arg (fun r : Modules.SkyscraperSections (genericPoint X) Ω[X.functionField⁄k] U ↦
    r ⟨(hWU x) hη⟩) hst

/-- **The local differentials.** The subspace `ω_x ⊆ Ω[K⁄k]` of germs of differentials regular
near `x` is the image of `Ω[𝒪_{X,x}⁄k] → Ω[K⁄k]`, where `𝒪_{X,x} ⊆ K` is the local ring
`AlgebraicGeometry.Scheme.localSubalgebra k X x`. -/
theorem coe_stalkLattice_differentialsToGeneric (x : X) :
    (Modules.stalkLattice k (differentialsToGeneric k X) x : Set Ω[X.functionField⁄k]) =
      Set.range (KaehlerDifferential.map k k (localSubalgebra k X x) X.functionField) := by
  ext v
  constructor
  · rintro ⟨U, hx, s, rfl⟩
    obtain ⟨W, hW, hxW, hWU⟩ := (Opens.isBasis_iff_nbhd.1 X.isBasis_affineOpens) hx
    have hη : genericPoint X ∈ W := genericPoint_mem_of_mem hxW
    let := ((X ↘ Spec (.of k)).specStructureMap W).hom.toAlgebra
    have hA : algebraMap k Γ(X, W) = ((X ↘ Spec (.of k)).specStructureMap W).hom := rfl
    obtain ⟨ω, hω⟩ := ((X ↘ Spec (.of k)).kaehlerSectionsEquiv W hA hW).surjective
      ((X ↘ Spec (.of k)).relativeDifferentials.presheaf.map (homOfLE hWU).op s)
    rw [← Modules.genericValue_res _ hWU hη, ← hω]
    have hmem (b : Γ(X, W)) : X.presheaf.germ W _ hη b ∈ localSubalgebra k X x :=
      ⟨W, hxW, b, rfl⟩
    refine genericValue_kaehlerSectionsEquiv_induction k hW hη hA
      (· ∈ Set.range (KaehlerDifferential.map k k (localSubalgebra k X x) X.functionField))
      ⟨0, map_zero _⟩ ?_ ?_ ?_ ω
    · rintro _ _ ⟨w, rfl⟩ ⟨w', rfl⟩
      exact ⟨w + w', map_add _ _ _⟩
    · rintro a _ ⟨w, rfl⟩
      refine ⟨(⟨_, hmem a⟩ : localSubalgebra k X x) • w, ?_⟩
      rw [LinearMap.map_smul, ← algebraMap_smul X.functionField]
      rfl
    · intro b
      exact ⟨KaehlerDifferential.D k (localSubalgebra k X x) ⟨_, hmem b⟩,
        KaehlerDifferential.map_D k k (localSubalgebra k X x) X.functionField _⟩
  · rintro ⟨w, rfl⟩
    have hw : w ∈ Submodule.span (localSubalgebra k X x)
        (Set.range (KaehlerDifferential.D k (localSubalgebra k X x))) :=
      (KaehlerDifferential.span_range_derivation k (localSubalgebra k X x)).symm ▸
        Submodule.mem_top
    induction hw using Submodule.span_induction with
    | mem w hw =>
      obtain ⟨⟨g, U, hx, a, rfl⟩, rfl⟩ := hw
      rw [KaehlerDifferential.map_D]
      exact ⟨U, hx, _, genericValue_differentialsToGeneric_sectionsD k _ a⟩
    | zero => rw [map_zero]; exact Submodule.zero_mem _
    | add w w' _ _ hw hw' => rw [map_add]; exact Submodule.add_mem _ hw hw'
    | smul o w _ hw =>
      obtain ⟨g, U, hx, a, rfl⟩ := o
      rw [LinearMap.map_smul, ← algebraMap_smul X.functionField]
      exact Modules.germ_smul_mem_stalkLattice _ hx a hw

section Curve

variable [NoetherianSpace X] (hdim : topologicalKrullDim X ≤ 1)

/-- The principal parts map `Ω[K⁄k] → ⨁_{x closed} Ω[K⁄k] ⧸ ω_x`. -/
noncomputable def differentialsPrincipalPartsMap :
    Ω[X.functionField⁄k] →ₗ[k]
      Π₀ x : closedPoints X,
        Ω[X.functionField⁄k] ⧸ Modules.stalkLattice k (differentialsToGeneric k X) x.1 :=
  Modules.principalPartsMap k (differentialsToGeneric k X) hdim
    (mem_stalkLattice_differentialsToGeneric_genericPoint k X)

@[simp]
lemma differentialsPrincipalPartsMap_apply (v : Ω[X.functionField⁄k]) (x : closedPoints X) :
    differentialsPrincipalPartsMap k hdim v x = Submodule.Quotient.mk v :=
  rfl

variable [Smooth (X ↘ Spec (.of k))]

/-- **`H¹(X, ω)` via principal parts of differentials.** For `X` integral, smooth over `k` and
of dimension at most one (e.g. a smooth proper connected curve), the residue sequence
`0 ⟶ ω ⟶ Ω[K⁄k]_η ⟶ 𝒫 ⟶ 0` gives a canonical `k`-linear isomorphism
`H¹(X, ω) ≅ (⨁_{x closed} Ω[K⁄k] ⧸ ω_x) ⧸ Ω[K⁄k]`, where
`ω_x = image(Ω[𝒪_{X,x}⁄k] → Ω[K⁄k])` (`coe_stalkLattice_differentialsToGeneric`).

(blueprint: `theorem-riemann-roch-coherent-serre-duality--2`) -/
noncomputable def differentialsH1Equiv :
    Modules.H (X ↘ Spec (.of k)).relativeDifferentials 1 ≃ₗ[k]
      (Π₀ x : closedPoints X,
        Ω[X.functionField⁄k] ⧸ Modules.stalkLattice k (differentialsToGeneric k X) x.1) ⧸
        LinearMap.range (differentialsPrincipalPartsMap k hdim) :=
  Modules.adelicH1Equiv k hdim (mem_stalkLattice_differentialsToGeneric_genericPoint k X)
    (injective_differentialsToGeneric_app k)

lemma differentialsH1Equiv_symm_mk
    (d : Π₀ x : closedPoints X,
      Ω[X.functionField⁄k] ⧸ Modules.stalkLattice k (differentialsToGeneric k X) x.1) :
    (differentialsH1Equiv k hdim).symm (Submodule.Quotient.mk d) =
      Modules.adelicToH1 k hdim (mem_stalkLattice_differentialsToGeneric_genericPoint k X)
        (injective_differentialsToGeneric_app k) d :=
  rfl

omit [NoetherianSpace X] in
/-- `H⁰(X, ω) ≅ ⋂_{x closed} ω_x`. -/
noncomputable def differentialsH0Equiv :
    Modules.H (X ↘ Spec (.of k)).relativeDifferentials 0 ≃ₗ[k]
      ↥(⨅ x : closedPoints X, Modules.stalkLattice k (differentialsToGeneric k X) x.1) :=
  Modules.adelicH0Equiv k hdim (mem_stalkLattice_differentialsToGeneric_genericPoint k X)
    (injective_differentialsToGeneric_app k)

end Curve

end AlgebraicGeometry.Scheme
