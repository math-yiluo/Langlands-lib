/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Cohomology.Defs
public import WeilConjectures.AlgebraicGeometry.DualNumbers
public import WeilConjectures.AlgebraicGeometry.Modules.PullbackFreeGenerator
public import WeilConjectures.AlgebraicGeometry.Sites.GmPicard
public import WeilConjectures.CategoryTheory.Sites.Torsor
public import WeilConjectures.Mathlib.Algebra.DualNumber

/-!
# The Picard group of the dual-number thickening

Let `X` be a scheme and `X[ε]` its dual-number thickening
(`AlgebraicGeometry.Scheme.dualNumbers`), with the closed immersion `i : X ⟶ X[ε]`. The
invertible modules on `X[ε]` which become trivial on `X` are classified by `H¹(X, 𝒪_X)`:

`ker (Pic(X[ε]) → Pic(X)) ≅ H¹(X, 𝒪_X)`,

and under this isomorphism rescaling the infinitesimal, `ε ↦ cε`, is multiplication by `c`.

## Main statements

- `AlgebraicGeometry.Scheme.exists_addEquiv_ker_picMap_dualNumbersι`: the isomorphism
  `ker (Pic(X[ε]) → Pic(X)) ≅ H¹(X, 𝒪_X)`, compatible with rescaling the infinitesimal.

## Implementation details

The two schemes have the same underlying space, so all sheaves live on the site of opens of
`X`. The units of `𝒪_{X[ε]} = 𝒪_X[ε]` split as `𝒪_{X[ε]}ˣ ≅ 𝒪_X ⊕ 𝒪_Xˣ`,
`a + εb ↦ (a⁻¹ b, a)`, compatibly with the inclusion `g ↦ 1 + εg` of `𝒪_X` and with
`a + εb ↦ a`, which corresponds to the pullback along `i` under
`Pic ≅ H¹(-, 𝒪ˣ)` (`AlgebraicGeometry.Scheme.Pic.toH1UnitsAddEquiv`). Taking `H¹` of this
splitting gives the isomorphism; no long exact sequence is needed.
-/

@[expose] public section

universe u

open CategoryTheory Opposite

namespace AlgebraicGeometry.Scheme

variable (X : Scheme.{u})

/-- The structure sheaf `𝒪_X` as a sheaf of abelian groups on the opens of `X`; its first
cohomology is `(Modules.unit X).H 1`. -/
noncomputable abbrev structureAddSheaf : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u} :=
  (SheafOfModules.toSheaf X.ringCatSheaf).obj (Modules.unit X)

/-- The sheaf `𝒪_{X[ε]}ˣ` of units of the dual-number thickening, on the opens of `X`: the two
schemes have the same underlying space. -/
noncomputable def dualNumbersUnitsSheaf : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u} :=
  X.dualNumbers.unitsSheaf

/-- `Pic(X[ε]) ≅ H¹(𝒪_{X[ε]}ˣ)` (`AlgebraicGeometry.Scheme.Pic.toH1Units`), with the cohomology
computed on the opens of `X`. -/
noncomputable def Pic.toH1UnitsDualNumbers :
    X.dualNumbers.Pic ≃ (Sheaf.H X.dualNumbersUnitsSheaf 1 : Type u) :=
  Pic.toH1Units X.dualNumbers

/-- `Pic(X[ε]) ≅ H¹(𝒪_{X[ε]}ˣ)` as an isomorphism of groups. -/
noncomputable def Pic.toH1UnitsDualNumbersAddEquiv :
    Additive X.dualNumbers.Pic ≃+ (Sheaf.H X.dualNumbersUnitsSheaf 1 : Type u) :=
  Pic.toH1UnitsAddEquiv X.dualNumbers

variable {X} in
lemma Pic.toH1UnitsDualNumbers_mk (M : X.dualNumbers.Modules)
    [SheafOfModules.IsInvertible.{u, u, u} M] :
    Pic.toH1UnitsDualNumbers X (Pic.mk M) =
      Sheaf.Torsor.classH1 X.dualNumbersUnitsSheaf (Limits.isTerminalTop (α := X.Opens))
        ⟦M.generatorsTorsor⟧ :=
  Pic.toH1Units_mk M

end AlgebraicGeometry.Scheme

namespace DualNumber

open TrivSqZeroExt

variable {R S : Type*} [CommRing R] [CommRing S]

/-- The units `1 + εg` are compatible with ring homomorphisms. -/
theorem oneAddEps_mapRingHom (f : R →+* S) (g : R) :
    oneAddEps (f g) = (Units.map (mapRingHom f).toMonoidHom).toAdditive (oneAddEps g) := by
  refine congrArg Additive.ofMul (Units.ext ?_)
  change 1 + inr (f g) = mapRingHom f (1 + inr g)
  ext <;> simp

/-- The `ε`-part of units is compatible with ring homomorphisms. -/
theorem unitsRetract_mapRingHom (f : R →+* S) (u : Additive R[ε]ˣ) :
    unitsRetract ((Units.map (mapRingHom f).toMonoidHom).toAdditive u) = f (unitsRetract u) := by
  rw [unitsRetract_apply, unitsRetract_apply]
  change (mapRingHom f (((Additive.toMul u)⁻¹ : R[ε]ˣ) : R[ε])).fst *
    (mapRingHom f ((Additive.toMul u : R[ε]ˣ) : R[ε])).snd = _
  rw [fst_mapRingHom, snd_mapRingHom, map_mul]

end DualNumber

namespace AlgebraicGeometry.Scheme

open DualNumber

variable (X : Scheme.{u})

/-- Restricting a global section in two steps. -/
lemma presheaf_map_homOfLE_top_apply (c : Γ(X, ⊤)) {U V : X.Opensᵒᵖ} (i : U ⟶ V) :
    X.presheaf.map i (X.presheaf.map (homOfLE le_top : U.unop ⟶ ⊤).op c) =
      X.presheaf.map (homOfLE le_top : V.unop ⟶ ⊤).op c := by
  rw [← CommRingCat.comp_apply, ← Functor.map_comp]
  rfl

/-- The inclusion `𝒪_X ⟶ 𝒪_{X[ε]}ˣ`, `g ↦ 1 + εg`, of sheaves of abelian groups on the opens
of `X`. -/
noncomputable def dualNumbersOneAddEps : X.structureAddSheaf ⟶ X.dualNumbersUnitsSheaf :=
  ObjectProperty.homMk
    { app U := AddCommGrpCat.ofHom (oneAddEps (R := Γ(X, U.unop)))
      naturality U V i := by
        ext g
        exact oneAddEps_mapRingHom (X.presheaf.map i).hom g }

/-- The reduction `𝒪_{X[ε]}ˣ ⟶ 𝒪_Xˣ`, `a + εb ↦ a`. -/
noncomputable def dualNumbersUnitsFst : X.dualNumbersUnitsSheaf ⟶ X.unitsSheaf :=
  ObjectProperty.homMk
    { app U := AddCommGrpCat.ofHom (unitsFst (R := Γ(X, U.unop)))
      naturality U V i := by
        ext u
        refine congrArg Additive.ofMul (Units.ext ?_)
        exact (fst_mapRingHom (X.presheaf.map i).hom _) }

/-- The inclusion `𝒪_Xˣ ⟶ 𝒪_{X[ε]}ˣ` of the units of `𝒪_X`. -/
noncomputable def dualNumbersUnitsInl : X.unitsSheaf ⟶ X.dualNumbersUnitsSheaf :=
  ObjectProperty.homMk
    { app U := AddCommGrpCat.ofHom (unitsInl (R := Γ(X, U.unop)))
      naturality U V i := by
        ext u
        refine congrArg Additive.ofMul (Units.ext ?_)
        change (TrivSqZeroExt.inl
          (X.presheaf.map i ((Additive.toMul u : Γ(X, U.unop)ˣ) : Γ(X, U.unop))) :
          DualNumber Γ(X, V.unop)) = mapRingHom (X.presheaf.map i).hom (TrivSqZeroExt.inl _)
        ext <;> simp }

/-- The `ε`-part `𝒪_{X[ε]}ˣ ⟶ 𝒪_X`, `a + εb ↦ a⁻¹ b`, a retraction of
`AlgebraicGeometry.Scheme.dualNumbersOneAddEps`. -/
noncomputable def dualNumbersUnitsRetract : X.dualNumbersUnitsSheaf ⟶ X.structureAddSheaf :=
  ObjectProperty.homMk
    { app U := AddCommGrpCat.ofHom (unitsRetract (R := Γ(X, U.unop)))
      naturality U V i := by
        ext u
        exact unitsRetract_mapRingHom (X.presheaf.map i).hom u }

/-- Rescaling the infinitesimal on units, `a + εb ↦ a + εcb`. -/
noncomputable def dualNumbersUnitsScale (c : Γ(X, ⊤)) :
    X.dualNumbersUnitsSheaf ⟶ X.dualNumbersUnitsSheaf :=
  ObjectProperty.homMk
    { app U := AddCommGrpCat.ofHom
        (Units.map
          (scale (X.presheaf.map (homOfLE le_top : U.unop ⟶ ⊤).op c)).toMonoidHom).toAdditive
      naturality U V i := by
        ext u
        refine congrArg Additive.ofMul (Units.ext ?_)
        change scale _ (mapRingHom (X.presheaf.map i).hom _) =
          mapRingHom (X.presheaf.map i).hom (scale _ _)
        ext
        · simp only [DualNumber.fst_scale, DualNumber.fst_mapRingHom]
          try rfl
        · simp only [DualNumber.snd_mapRingHom, DualNumber.snd_scale, map_mul]
          exact congrArg (· * _) (X.presheaf_map_homOfLE_top_apply c i).symm }

@[reassoc (attr := simp)]
lemma dualNumbersOneAddEps_comp_unitsRetract :
    X.dualNumbersOneAddEps ≫ X.dualNumbersUnitsRetract = 𝟙 _ := by
  ext U g
  exact unitsRetract_oneAddEps (R := Γ(X, U.unop)) g

@[reassoc (attr := simp)]
lemma dualNumbersOneAddEps_comp_unitsFst : X.dualNumbersOneAddEps ≫ X.dualNumbersUnitsFst = 0 := by
  ext U g
  exact unitsFst_oneAddEps (R := Γ(X, U.unop)) g

@[reassoc (attr := simp)]
lemma dualNumbersUnitsInl_comp_unitsFst : X.dualNumbersUnitsInl ≫ X.dualNumbersUnitsFst = 𝟙 _ := by
  ext U a
  exact unitsFst_unitsInl (R := Γ(X, U.unop)) a

lemma dualNumbersUnitsRetract_comp_oneAddEps_add :
    X.dualNumbersUnitsRetract ≫ X.dualNumbersOneAddEps +
      X.dualNumbersUnitsFst ≫ X.dualNumbersUnitsInl = 𝟙 _ := by
  ext U u
  exact oneAddEps_unitsRetract_add_unitsInl_unitsFst (R := Γ(X, U.unop)) u

lemma dualNumbersUnitsScale_comp_unitsRetract (c : Γ(X, ⊤)) :
    X.dualNumbersUnitsScale c ≫ X.dualNumbersUnitsRetract =
      X.dualNumbersUnitsRetract ≫
        (SheafOfModules.toSheaf X.ringCatSheaf).map ((Modules.unit X).smulHom c) := by
  ext U u
  exact unitsRetract_map_scale (R := Γ(X, U.unop)) _ u

section Torsor

open Modules

variable {X}

/-- The section of `𝒪_X` restricting a unit `a + εb` along `i : X ⟶ X[ε]` is `a`. -/
lemma dualNumbersι_app_apply (U : X.Opens) (a : Γ(X.dualNumbers, U)) :
    X.dualNumbersι.app U a = a.fst :=
  rfl

/-- **Restriction to `X` on `H¹(𝒪ˣ)`.** Under `Pic ≅ H¹(-, 𝒪ˣ)`, the pullback along the closed
immersion `i : X ⟶ X[ε]` is induced by the reduction `𝒪_{X[ε]}ˣ ⟶ 𝒪_Xˣ`, `a + εb ↦ a`: a
generator `s` of `ℒ` goes to the generator `i^* s` of `i^* ℒ`. -/
lemma Pic.toH1Units_map_dualNumbersι (L : X.dualNumbers.Pic) :
    Pic.toH1Units X (Pic.map X.dualNumbersι L) =
      Sheaf.H.map X.dualNumbersUnitsFst 1 (Pic.toH1UnitsDualNumbers X L) := by
  let M := (fromSkeleton X.dualNumbers.Modules).obj L.val
  have := Pic.isInvertible L
  have : SheafOfModules.IsInvertible.{u, u, u} ((pullback X.dualNumbersι).obj M) :=
    SheafOfModules.IsInvertible.pullback (g := X.dualNumbersι) (M := M) (Pic.isInvertible L)
  have h₁ : Pic.map X.dualNumbersι L = Pic.mk ((pullback X.dualNumbersι).obj M) := Pic.ext rfl
  rw [h₁, Pic.toH1Units_mk]
  refine Sheaf.Torsor.classH1_eq_map_of_equivariant _ _ M.generatorsTorsor _
    (fun U s ↦ ⟨pullbackSection X.dualNumbersι (show Γ(M, U.unop) from s.1),
      IsFreeGenerator.pullback_unit_app X.dualNumbersι s.2⟩) (fun U V f s ↦ ?_)
    (fun U a s ↦ ?_)
  · exact Subtype.ext (pullbackSection_map X.dualNumbersι (leOfHom f.unop) s.1).symm
  · exact Subtype.ext (pullbackSection_smul X.dualNumbersι _ (show Γ(M, U.unop) from s.1))

/-- **Rescaling the infinitesimal on `H¹(𝒪ˣ)`.** Under `Pic ≅ H¹(-, 𝒪ˣ)`, the pullback along
`ε ↦ cε` is induced by `a + εb ↦ a + εcb` on units. -/
lemma Pic.toH1Units_map_dualNumbersScale (c : Γ(X, ⊤)) (L : X.dualNumbers.Pic) :
    Pic.toH1UnitsDualNumbers X (Pic.map (X.dualNumbersScale c) L) =
      Sheaf.H.map (X.dualNumbersUnitsScale c) 1 (Pic.toH1UnitsDualNumbers X L) := by
  let M := (fromSkeleton X.dualNumbers.Modules).obj L.val
  have := Pic.isInvertible L
  have : SheafOfModules.IsInvertible.{u, u, u} ((pullback (X.dualNumbersScale c)).obj M) :=
    SheafOfModules.IsInvertible.pullback (g := X.dualNumbersScale c) (M := M) (Pic.isInvertible L)
  have h₁ : Pic.map (X.dualNumbersScale c) L = Pic.mk ((pullback (X.dualNumbersScale c)).obj M) :=
    Pic.ext rfl
  rw [h₁, Pic.toH1UnitsDualNumbers_mk]
  refine Sheaf.Torsor.classH1_eq_map_of_equivariant _ _ M.generatorsTorsor _
    (fun U s ↦ ⟨pullbackSection (X.dualNumbersScale c) (show Γ(M, U.unop) from s.1),
      IsFreeGenerator.pullback_unit_app (X.dualNumbersScale c) s.2⟩) (fun U V f s ↦ ?_)
    (fun U a s ↦ ?_)
  · exact Subtype.ext (pullbackSection_map (X.dualNumbersScale c) (leOfHom f.unop) s.1).symm
  · exact Subtype.ext
      (pullbackSection_smul (X.dualNumbersScale c) _ (show Γ(M, U.unop) from s.1))

end Torsor

section Kernel

variable {X}

lemma Pic.toH1Units_one : Pic.toH1Units X 1 = 0 :=
  (Pic.toH1UnitsAddEquiv X).map_zero

lemma Pic.toH1Units_eq_zero_iff (L : X.Pic) : Pic.toH1Units X L = 0 ↔ L = 1 := by
  rw [← Pic.toH1Units_one, (Pic.toH1Units X).injective.eq_iff]

/-- The decomposition of `H¹(𝒪_{X[ε]}ˣ)` given by the splitting `𝒪_{X[ε]}ˣ ≅ 𝒪_X ⊕ 𝒪_Xˣ`. -/
lemma sheafH_map_dualNumbersUnitsRetract_add
    (x : (Sheaf.H X.dualNumbersUnitsSheaf 1 : Type u)) :
    Sheaf.H.map X.dualNumbersOneAddEps 1 (Sheaf.H.map X.dualNumbersUnitsRetract 1 x) +
      Sheaf.H.map X.dualNumbersUnitsInl 1 (Sheaf.H.map X.dualNumbersUnitsFst 1 x) = x := by
  rw [← Sheaf.H.map_comp_apply, ← Sheaf.H.map_comp_apply, ← Sheaf.H.map_add_apply,
    dualNumbersUnitsRetract_comp_oneAddEps_add, Sheaf.H.map_id_apply]

variable (X) in
/-- **Invertible modules on `X[ε]` trivial on `X` are classified by `H¹(X, 𝒪_X)`.** For a
scheme `X` with dual-number thickening `i : X ⟶ X[ε]`, the kernel of
`i^* : Pic(X[ε]) → Pic(X)` is isomorphic to `H¹(X, 𝒪_X)`, compatibly with the scalar actions:
the pullback along `ε ↦ cε` corresponds to multiplication by `c ∈ Γ(X, 𝒪_X)`. -/
theorem exists_addEquiv_ker_picMap_dualNumbersι :
    ∃ Ψ : Additive (Pic.mapHom X.dualNumbersι).ker ≃+ (Modules.unit X).H 1,
      ∀ (c : Γ(X, ⊤)) (L L' : (Pic.mapHom X.dualNumbersι).ker),
        L'.1 = Pic.map (X.dualNumbersScale c) L.1 → Ψ (.ofMul L') = c • Ψ (.ofMul L) := by
  let r : (Sheaf.H X.dualNumbersUnitsSheaf 1 : Type u) →+
      (Sheaf.H X.structureAddSheaf 1 : Type u) :=
    Sheaf.H.map X.dualNumbersUnitsRetract 1
  let Ψ₀ : Additive (Pic.mapHom X.dualNumbersι).ker →+ (Sheaf.H X.structureAddSheaf 1 : Type u) :=
    r.comp ((Pic.toH1UnitsDualNumbersAddEquiv X).toAddMonoidHom.comp
      (Pic.mapHom X.dualNumbersι).ker.subtype.toAdditive)
  have hΨ₀ (L : (Pic.mapHom X.dualNumbersι).ker) :
      Ψ₀ (.ofMul L) = Sheaf.H.map X.dualNumbersUnitsRetract 1 (Pic.toH1UnitsDualNumbers X L.1) :=
    rfl
  have hker (L : X.dualNumbers.Pic) :
      L ∈ (Pic.mapHom X.dualNumbersι).ker ↔
        Sheaf.H.map X.dualNumbersUnitsFst 1 (Pic.toH1UnitsDualNumbers X L) =
          (0 : (Sheaf.H X.unitsSheaf 1 : Type u)) := by
    rw [MonoidHom.mem_ker, Pic.mapHom_apply, ← Pic.toH1Units_eq_zero_iff,
      Pic.toH1Units_map_dualNumbersι]
  have hinj : Function.Injective Ψ₀ := by
    refine (injective_iff_map_eq_zero Ψ₀).2 fun L hL ↦ ?_
    have h := sheafH_map_dualNumbersUnitsRetract_add (Pic.toH1UnitsDualNumbers X L.toMul.1)
    have hL' : r (Pic.toH1UnitsDualNumbers X L.toMul.1) = 0 := hL
    change Sheaf.H.map X.dualNumbersOneAddEps 1 (r _) + _ = _ at h
    rw [hL', (hker _).1 L.toMul.2, map_zero, map_zero, add_zero, eq_comm] at h
    exact Additive.toMul.injective (Subtype.ext ((Pic.toH1Units_eq_zero_iff _).1 h))
  have hsurj : Function.Surjective Ψ₀ := fun y ↦ by
    let L := (Pic.toH1UnitsDualNumbers X).symm (Sheaf.H.map X.dualNumbersOneAddEps 1 y)
    have hL' : Pic.toH1UnitsDualNumbers X L = Sheaf.H.map X.dualNumbersOneAddEps 1 y :=
      Equiv.apply_symm_apply _ _
    have hL : L ∈ (Pic.mapHom X.dualNumbersι).ker := by
      rw [hker, hL', ← Sheaf.H.map_comp_apply, dualNumbersOneAddEps_comp_unitsFst]
      have h0 := Sheaf.H.map_add_apply (0 : X.structureAddSheaf ⟶ X.unitsSheaf) 0 y
      rw [add_zero] at h0
      exact left_eq_add.mp h0
    refine ⟨.ofMul ⟨L, hL⟩, ?_⟩
    rw [hΨ₀]
    change r (Pic.toH1UnitsDualNumbers X L) = y
    rw [hL']
    change Sheaf.H.map X.dualNumbersUnitsRetract 1 (Sheaf.H.map X.dualNumbersOneAddEps 1 y) = y
    rw [← Sheaf.H.map_comp_apply, dualNumbersOneAddEps_comp_unitsRetract, Sheaf.H.map_id_apply]
  refine ⟨AddEquiv.ofBijective Ψ₀ ⟨hinj, hsurj⟩, fun c L L' h ↦ ?_⟩
  have key : Ψ₀ (.ofMul L') = Sheaf.H.map
      ((SheafOfModules.toSheaf X.ringCatSheaf).map ((Modules.unit X).smulHom c)) 1
        (Ψ₀ (.ofMul L)) := by
    rw [hΨ₀, hΨ₀, h, Pic.toH1Units_map_dualNumbersScale]
    refine (Sheaf.H.map_comp_apply (X.dualNumbersUnitsScale c) X.dualNumbersUnitsRetract
      _).symm.trans ?_
    exact (congrArg (fun φ ↦ Sheaf.H.map φ 1 _) (dualNumbersUnitsScale_comp_unitsRetract X c)).trans
      (Sheaf.H.map_comp_apply _ _ _)
  exact key

end Kernel

end AlgebraicGeometry.Scheme
