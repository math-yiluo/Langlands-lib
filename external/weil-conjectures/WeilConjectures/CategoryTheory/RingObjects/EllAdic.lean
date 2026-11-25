/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import Mathlib.AlgebraicGeometry.Sites.ElladicCohomology
public import WeilConjectures.CategoryTheory.RingObjects.ContinuousMap
public import WeilConjectures.NumberTheory.Padics.Extension

/-!

# The `ℓ`-adic coefficient sheaves `ℤ_ℓ`, `ℚ_ℓ`, `E` and `ℚ̄_ℓ` as ring objects

Let `X` be a scheme and `ℓ` a prime. Following Section 6.8 of
*Bhargav Bhatt and Peter Scholze, The pro-étale topology for schemes*, the coefficient
sheaves of `ℓ`-adic cohomology are sheaves of rings on the small pro-étale site `X_proét`.
This file constructs them as sheaves of rings; their underlying abelian sheaves, through
`sheafCompose _ (forget₂ RingCat Ab)`, are then ring objects of the category of abelian
sheaves on `X_proét` (`CategoryTheory.Sheaf.monObj_sheafCompose_obj`), with the monoidal
structure given by the sheafification of the objectwise tensor product
(`AlgebraicGeometry.ProEtale.sheafMonoidalCategory`).

* `ℤ_ℓ,X` and `ℚ_ℓ,X` are the sheaves of continuous maps `U ↦ C(U, ℤ_ℓ)` and `U ↦ C(U, ℚ_ℓ)`
  with the pointwise ring structure (`ProEtale.padicIntSheaf`, `ProEtale.padicSheaf`). The
  abelian sheaf underlying the former is mathlib's `ℓ`-adic sheaf
  `AlgebraicGeometry.Scheme.ellAdicSheaf` lifted to the universe `u + 1`, definitionally
  (`ProEtale.sheafCompose_obj_padicIntSheaf`).
* For a subfield `E` of `ℚ̄_ℓ = PadicAlgCl ℓ`, given by an embedding `E → ℚ̄_ℓ` as in
  `WeilConjectures.NumberTheory.Padics.Extension`, `E_X` and `𝒪_{E,X}` are the sheaves of
  continuous maps `U ↦ C(U, E)` and `U ↦ C(U, 𝒪_E)`, for the topologies of `E` and of its ring
  of integers `𝒪_E` restricted from `ℚ̄_ℓ` (`ProEtale.padicSubfieldSheaf`,
  `ProEtale.padicIntegersSheaf`).
* `ℚ̄_ℓ,X` is **not** the sheaf of continuous maps into `ℚ̄_ℓ` with its valuation topology:
  the sections of the correct `ℚ̄_ℓ`-sheaf over a w-contractible `U` are the continuous maps
  `U → ℚ̄_ℓ` taking values in some *finite* subextension `E ⊆ ℚ̄_ℓ` of `ℚ_ℓ`, which is a
  strictly smaller ring than `C(U, ℚ̄_ℓ)` (a sequence of elements of unbounded degree
  converging to `0` in `ℚ̄_ℓ` extends to a continuous map on the Stone–Čech compactification
  of `ℕ`, which is w-contractible). Accordingly `ℚ̄_ℓ,X` is defined as the sheafification of
  the presheaf of rings `U ↦ {f ∈ C(U, ℚ̄_ℓ) | f takes values in a finite subextension}`
  (`PadicAlgCl.finiteIntermediateFieldValued`, `ProEtale.padicAlgClSheaf`). This presheaf is the
  union of the presheaves `U ↦ C(U, E)` over the finite subextensions `E ⊆ ℚ̄_ℓ`, so that
  `ℚ̄_ℓ,X = colim_E E_X` as sheaves of rings, which is the `ℚ̄_ℓ`-sheaf of Bhatt–Scholze
  (`ProEtale.isColimitPadicAlgClSheafCocone`, as abelian sheaves, over the directed
  set `PadicAlgCl.FiniteIntermediateField`). It is defined directly as a
  ring object of abelian sheaves, the sheafification of presheaves of rings not being
  available.

All of these are commutative ring objects, and the natural inclusions
`ℤ_ℓ,X ⟶ ℚ_ℓ,X ⟶ E_X ⟶ ℚ̄_ℓ,X`, `ℤ_ℓ,X ⟶ 𝒪_{E,X} ⟶ E_X` and `ℚ_ℓ,X ⟶ ℚ̄_ℓ,X` are morphisms of
ring objects.

## Main definitions

* `AlgebraicGeometry.ProEtale.padicIntSheaf`: the sheaf of rings `ℤ_ℓ,X`.
* `AlgebraicGeometry.ProEtale.padicSheaf`: the sheaf of rings `ℚ_ℓ,X`.
* `AlgebraicGeometry.ProEtale.padicSubfieldSheaf` and
  `AlgebraicGeometry.ProEtale.padicIntegersSheaf`: the sheaves of rings `E_X` and `𝒪_{E,X}` for
  `E ⊆ ℚ̄_ℓ`.
* `AlgebraicGeometry.ProEtale.padicAlgClSheaf`: the ring object `ℚ̄_ℓ,X` of abelian sheaves.
* `AlgebraicGeometry.ProEtale.padicIntSheafToPadicSheaf`,
  `AlgebraicGeometry.ProEtale.padicSheafToPadicSubfieldSheaf`,
  `AlgebraicGeometry.ProEtale.padicIntegersSheafToPadicSubfieldSheaf` and
  `AlgebraicGeometry.ProEtale.padicIntSheafToPadicIntegersSheaf`: the inclusions, as morphisms
  of sheaves of rings; `AlgebraicGeometry.ProEtale.padicSheafToPadicAlgClSheaf` and
  `AlgebraicGeometry.ProEtale.padicSubfieldSheafToPadicAlgClSheaf`: the inclusions into
  `ℚ̄_ℓ,X`, as morphisms of ring objects.
* `AlgebraicGeometry.ProEtale.padicAlgClSheafCocone`: the cocone of the `E_X ⟶ ℚ̄_ℓ,X` over the
  finite subextensions `E`, and `AlgebraicGeometry.ProEtale.isColimitPadicAlgClSheafCocone`: it
  is a colimit, being the sheafification of the colimit `padicAlgClPresheafCocone` of
  presheaves.

-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory MonObj Limits Opposite

namespace PadicAlgCl

variable (ℓ : ℕ) [Fact ℓ.Prime] (U : Type*) [TopologicalSpace U]

/-- The subring of `C(U, ℚ̄_ℓ)` of continuous maps whose values lie in some finite subextension
`E ⊆ ℚ̄_ℓ` of `ℚ_ℓ`. Sums and products of such maps take values in the compositum of the two
subextensions, which is again finite. -/
def finiteIntermediateFieldValued : Subring C(U, PadicAlgCl ℓ) where
  carrier := {f | ∃ E : IntermediateField ℚ_[ℓ] (PadicAlgCl ℓ),
    FiniteDimensional ℚ_[ℓ] E ∧ ∀ x, f x ∈ E}
  mul_mem' := by
    rintro f g ⟨E, hE, hf⟩ ⟨F, hF, hg⟩
    refine ⟨E ⊔ F, by have := hE; have := hF; infer_instance, fun x ↦ ?_⟩
    rw [ContinuousMap.mul_apply]
    exact mul_mem (IsConcreteLE.le_iff.mp le_sup_left (hf x))
      (IsConcreteLE.le_iff.mp le_sup_right (hg x))
  add_mem' := by
    rintro f g ⟨E, hE, hf⟩ ⟨F, hF, hg⟩
    refine ⟨E ⊔ F, by have := hE; have := hF; infer_instance, fun x ↦ ?_⟩
    rw [ContinuousMap.add_apply]
    exact add_mem (IsConcreteLE.le_iff.mp le_sup_left (hf x))
      (IsConcreteLE.le_iff.mp le_sup_right (hg x))
  one_mem' := ⟨⊥, inferInstance, fun _ ↦ one_mem ⊥⟩
  zero_mem' := ⟨⊥, inferInstance, fun _ ↦ zero_mem ⊥⟩
  neg_mem' := by
    rintro f ⟨E, hE, hf⟩
    exact ⟨E, hE, fun x ↦ neg_mem (hf x)⟩

lemma mem_finiteIntermediateFieldValued_iff (f : C(U, PadicAlgCl ℓ)) :
    f ∈ finiteIntermediateFieldValued ℓ U ↔
      ∃ E : IntermediateField ℚ_[ℓ] (PadicAlgCl ℓ), FiniteDimensional ℚ_[ℓ] E ∧ ∀ x, f x ∈ E :=
  Iff.rfl

/-- The finite subextensions `E ⊆ ℚ̄_ℓ` of `ℚ_ℓ`, ordered by inclusion. This is a directed
order, the compositum of two finite subextensions being finite. -/
abbrev FiniteIntermediateField : Type :=
  {E : IntermediateField ℚ_[ℓ] (PadicAlgCl ℓ) // FiniteDimensional ℚ_[ℓ] E}

instance (E : FiniteIntermediateField ℓ) : FiniteDimensional ℚ_[ℓ] E.1 := E.2

instance : Nonempty (FiniteIntermediateField ℓ) := ⟨⟨⊥, inferInstance⟩⟩

instance : IsDirectedOrder (FiniteIntermediateField ℓ) where
  directed E F := ⟨⟨E.1 ⊔ F.1, inferInstance⟩, le_sup_left (a := E.1), le_sup_right (a := E.1)⟩

end PadicAlgCl

namespace AlgebraicGeometry.ProEtale

open Scheme

variable (X : Scheme.{u}) (ℓ : ℕ) [Fact ℓ.Prime]

/-! ### `ℤ_ℓ` and `ℚ_ℓ` -/

/-- The sheaf of rings `ℤ_ℓ,X` on `X_proét`: the sheaf of continuous maps `U ↦ C(U, ℤ_ℓ)` with
the pointwise ring structure [Bhatt–Scholze, Definition 6.8.1]. Its underlying abelian sheaf is
mathlib's `ℓ`-adic sheaf `AlgebraicGeometry.Scheme.ellAdicSheaf`, see
`ProEtale.sheafCompose_obj_padicIntSheaf`. -/
noncomputable abbrev padicIntSheaf : Sheaf (ProEt.topology X) RingCat.{u + 1} :=
  continuousMapRingSheaf X ℤ_[ℓ]

/-- The abelian sheaf underlying `ℤ_ℓ,X` is mathlib's `ℓ`-adic sheaf
`AlgebraicGeometry.Scheme.ellAdicSheaf`, lifted to the universe `u + 1`. -/
lemma sheafCompose_obj_padicIntSheaf :
    (sheafCompose (ProEt.topology X) (forget₂ RingCat.{u + 1} Ab.{u + 1})).obj
        (padicIntSheaf X ℓ) =
      (sheafCompose (ProEt.topology X) AddCommGrpCat.uliftFunctor.{u + 1}).obj
        (X.ellAdicSheaf ℓ) :=
  rfl


/-- The sheaf of rings `ℚ_ℓ,X` on `X_proét`: the sheaf of continuous maps `U ↦ C(U, ℚ_ℓ)` with
the pointwise ring structure [Bhatt–Scholze, Definition 6.8.1]. -/
noncomputable abbrev padicSheaf : Sheaf (ProEt.topology X) RingCat.{u + 1} :=
  continuousMapRingSheaf X ℚ_[ℓ]

/-- The inclusion `ℤ_ℓ,X ⟶ ℚ_ℓ,X`, a morphism of sheaves of rings. -/
noncomputable def padicIntSheafToPadicSheaf : padicIntSheaf X ℓ ⟶ padicSheaf X ℓ :=
  continuousMapRingSheafMap X PadicInt.Coe.ringHom continuous_subtype_val

/-! ### Subfields `E` of `ℚ̄_ℓ` -/

section Subfield

variable (E : Type) [Field E] [Algebra E (PadicAlgCl ℓ)]

/-- The sheaf of rings `E_X` on `X_proét`, for a subfield `E` of `ℚ̄_ℓ` given by an embedding
`E → ℚ̄_ℓ`: the sheaf of continuous maps `U ↦ C(U, E)` with the pointwise ring structure, for
the topology of `E` restricted from `ℚ̄_ℓ` along the embedding
(`PadicAlgCl.normedFieldOfAlgebra`). -/
noncomputable abbrev padicSubfieldSheaf : Sheaf (ProEt.topology X) RingCat.{u + 1} :=
  letI := PadicAlgCl.normedFieldOfAlgebra ℓ E
  continuousMapRingSheaf X E

/-- The embedding `E → ℚ̄_ℓ` is continuous for the topology of `E` restricted from `ℚ̄_ℓ`. -/
lemma continuous_algebraMap_padicAlgCl_of_algebra :
    letI := PadicAlgCl.normedFieldOfAlgebra ℓ E
    Continuous (algebraMap E (PadicAlgCl ℓ)) :=
  continuous_induced_dom

variable [Algebra ℚ_[ℓ] E] [IsScalarTower ℚ_[ℓ] E (PadicAlgCl ℓ)]

/-- The structure map `ℚ_ℓ → E` is continuous for the topology of `E` restricted from `ℚ̄_ℓ`:
composed with the embedding `E → ℚ̄_ℓ` it is the continuous structure map `ℚ_ℓ → ℚ̄_ℓ`. -/
lemma continuous_algebraMap_padic_of_algebra :
    letI := PadicAlgCl.normedFieldOfAlgebra ℓ E
    Continuous (algebraMap ℚ_[ℓ] E) := by
  let := PadicAlgCl.normedFieldOfAlgebra ℓ E
  refine continuous_induced_rng.mpr ?_
  change Continuous ((algebraMap E (PadicAlgCl ℓ)) ∘ (algebraMap ℚ_[ℓ] E))
  rw [← RingHom.coe_comp, ← IsScalarTower.algebraMap_eq]
  exact continuous_algebraMap ℚ_[ℓ] (PadicAlgCl ℓ)

/-- The inclusion `ℚ_ℓ,X ⟶ E_X`, a morphism of sheaves of rings. -/
noncomputable def padicSheafToPadicSubfieldSheaf : padicSheaf X ℓ ⟶ padicSubfieldSheaf X ℓ E :=
  letI := PadicAlgCl.normedFieldOfAlgebra ℓ E
  continuousMapRingSheafMap X (algebraMap ℚ_[ℓ] E) (continuous_algebraMap_padic_of_algebra ℓ E)

end Subfield

/-! ### The rings of integers `𝒪_E` -/

section Integers

variable (E : Type) [Field E] [Algebra E (PadicAlgCl ℓ)]

/-- The sheaf of rings `𝒪_{E,X}` on `X_proét`, for a subfield `E` of `ℚ̄_ℓ` given by an embedding
`E → ℚ̄_ℓ`: the sheaf of continuous maps `U ↦ C(U, 𝒪_E)` with the pointwise ring structure
into the ring of integers `𝒪_E = PadicAlgCl.integers ℓ E` of `E`, for the topology of `𝒪_E`
restricted from `ℚ̄_ℓ` along the embedding. -/
noncomputable abbrev padicIntegersSheaf : Sheaf (ProEt.topology X) RingCat.{u + 1} :=
  letI := PadicAlgCl.normedFieldOfAlgebra ℓ E
  continuousMapRingSheaf X (PadicAlgCl.integers ℓ E)

/-- The inclusion `𝒪_{E,X} ⟶ E_X`, a morphism of sheaves of rings. -/
noncomputable def padicIntegersSheafToPadicSubfieldSheaf :
    padicIntegersSheaf X ℓ E ⟶ padicSubfieldSheaf X ℓ E :=
  letI := PadicAlgCl.normedFieldOfAlgebra ℓ E
  continuousMapRingSheafMap X (PadicAlgCl.integers ℓ E).subtype continuous_subtype_val

variable [Algebra ℚ_[ℓ] E] [IsScalarTower ℚ_[ℓ] E (PadicAlgCl ℓ)]

/-- The structure map `ℚ_ℓ → E` sends `ℤ_ℓ` into the ring of integers `𝒪_E`: the valuation of
`E` extends the `ℓ`-adic one. -/
lemma algebraMap_padicInt_mem_integers (x : ℤ_[ℓ]) :
    algebraMap ℚ_[ℓ] E x ∈ PadicAlgCl.integers ℓ E := by
  rw [PadicAlgCl.mem_integers_iff, ← IsScalarTower.algebraMap_apply]
  exact_mod_cast (PadicAlgCl.norm_extends ℓ (x : ℚ_[ℓ])).le.trans x.2

/-- The structure map `ℤ_ℓ → 𝒪_E`, the restriction of `ℚ_ℓ → E` to the rings of integers. -/
noncomputable def padicIntToIntegers : ℤ_[ℓ] →+* PadicAlgCl.integers ℓ E :=
  ((algebraMap ℚ_[ℓ] E).comp PadicInt.Coe.ringHom).codRestrict (PadicAlgCl.integers ℓ E)
    (algebraMap_padicInt_mem_integers ℓ E)

/-- The structure map `ℤ_ℓ → 𝒪_E` is continuous for the topology of `𝒪_E` restricted from
`ℚ̄_ℓ`. -/
lemma continuous_padicIntToIntegers :
    letI := PadicAlgCl.normedFieldOfAlgebra ℓ E
    Continuous (padicIntToIntegers ℓ E) := by
  let := PadicAlgCl.normedFieldOfAlgebra ℓ E
  refine continuous_induced_rng.mpr ?_
  exact (continuous_algebraMap_padic_of_algebra ℓ E).comp continuous_subtype_val

/-- The inclusion `ℤ_ℓ,X ⟶ 𝒪_{E,X}`, a morphism of sheaves of rings. -/
noncomputable def padicIntSheafToPadicIntegersSheaf :
    padicIntSheaf X ℓ ⟶ padicIntegersSheaf X ℓ E :=
  letI := PadicAlgCl.normedFieldOfAlgebra ℓ E
  continuousMapRingSheafMap X (padicIntToIntegers ℓ E) (continuous_padicIntToIntegers ℓ E)

end Integers

/-! ### `ℚ̄_ℓ` -/

/-- The presheaf of rings `U ↦ {f ∈ C(U, ℚ̄_ℓ) | f takes values in a finite subextension}` on
`X_proét`, the union over the finite subextensions `E ⊆ ℚ̄_ℓ` of `ℚ_ℓ` of the presheaves
`U ↦ C(U, E)`. Its sheafification is the ring object `ℚ̄_ℓ,X`. -/
noncomputable def padicAlgClRingPresheaf : X.ProEtᵒᵖ ⥤ RingCat.{u + 1} where
  obj U := RingCat.of (ULift.{u + 1} (PadicAlgCl.finiteIntermediateFieldValued ℓ U.unop.left))
  map f := RingCat.ofHom
    (ULift.ringEquiv.symm.toRingHom.comp
      (((((ContinuousMap.compRightAlgHom ℤ (PadicAlgCl ℓ) f.unop.left.base.hom).toRingHom).comp
          (PadicAlgCl.finiteIntermediateFieldValued ℓ _).subtype).codRestrict
          (PadicAlgCl.finiteIntermediateFieldValued ℓ _) (fun g ↦ by
            obtain ⟨E, hE, hg⟩ := g.2
            exact ⟨E, hE, fun x ↦ hg _⟩)).comp ULift.ringEquiv.toRingHom))
  map_id _ := rfl
  map_comp _ _ := rfl

lemma padicAlgClRingPresheaf_map_apply {U V : X.ProEtᵒᵖ} (f : U ⟶ V)
    (g : ULift.{u + 1} (PadicAlgCl.finiteIntermediateFieldValued ℓ U.unop.left)) :
    ((padicAlgClRingPresheaf X ℓ).map f g).down.1 = g.down.1.comp f.unop.left.base.hom :=
  rfl


/-- The ring object `ℚ̄_ℓ,X` of abelian sheaves on `X_proét`: the sheafification of the
presheaf of rings `U ↦ {f ∈ C(U, ℚ̄_ℓ) | f takes values in a finite subextension of ℚ_ℓ}`,
which is the union of the presheaves `U ↦ C(U, E)` over the finite subextensions `E ⊆ ℚ̄_ℓ`.
This is the `ℚ̄_ℓ`-sheaf of [Bhatt–Scholze, Section 6.8], `colim_E E_X`; it differs from the
sheaf of continuous maps into `ℚ̄_ℓ` with its valuation topology. -/
noncomputable abbrev padicAlgClSheaf : Sheaf (ProEt.topology X) Ab.{u + 1} :=
  Sheaf.sheafifyRingPresheaf.{u + 1, u, u + 1} (ProEt.topology X) (padicAlgClRingPresheaf X ℓ)

instance : IsCommMonObj (padicAlgClSheaf X ℓ) :=
  haveI := (padicAlgClRingPresheaf X ℓ).isCommMonObj_compForget₂ fun U
    (a b : ULift.{u + 1} (PadicAlgCl.finiteIntermediateFieldValued ℓ U.unop.left)) ↦ mul_comm a b
  inferInstance

section ToPadicAlgCl

variable {T : Type} [TopologicalSpace T] [Ring T] [IsTopologicalRing T]
  (ψ : T →+* PadicAlgCl ℓ) (hψ : Continuous ψ)
  (hE : ∃ E : IntermediateField ℚ_[ℓ] (PadicAlgCl ℓ), FiniteDimensional ℚ_[ℓ] E ∧ ∀ t, ψ t ∈ E)

/-- Postcomposition with a continuous ring homomorphism `ψ : T → ℚ̄_ℓ` whose image lies in a
finite subextension of `ℚ_ℓ`, as a morphism of presheaves of rings from `U ↦ C(U, T)` to the
presheaf of continuous maps into `ℚ̄_ℓ` with values in a finite subextension. -/
noncomputable def continuousMapRingPresheafToPadicAlgCl :
    continuousMapRingPresheaf X T ⟶ padicAlgClRingPresheaf X ℓ where
  app _ := RingCat.ofHom
    (ULift.ringEquiv.symm.toRingHom.comp
      (((ψ.compLeftContinuous _ hψ).codRestrict (PadicAlgCl.finiteIntermediateFieldValued ℓ _)
          (fun g ↦ by
            obtain ⟨E, hE, h⟩ := hE
            exact ⟨E, hE, fun x ↦ h (g x)⟩)).comp ULift.ringEquiv.toRingHom))
  naturality _ _ _ := rfl

/-- The morphism of ring objects `C(-, T) ⟶ ℚ̄_ℓ,X` induced by a continuous ring homomorphism
`ψ : T → ℚ̄_ℓ` whose image lies in a finite subextension of `ℚ_ℓ`. -/
noncomputable def continuousMapRingSheafToPadicAlgClSheaf :
    (sheafCompose (ProEt.topology X) (forget₂ RingCat.{u + 1} Ab.{u + 1})).obj
      (continuousMapRingSheaf X T) ⟶ padicAlgClSheaf X ℓ :=
  Sheaf.sheafComposeToSheafify (ProEt.topology X) (continuousMapRingSheaf X T)
    (continuousMapRingPresheafToPadicAlgCl X ℓ ψ hψ hE)

instance : IsMonHom (continuousMapRingSheafToPadicAlgClSheaf X ℓ ψ hψ hE) :=
  inferInstanceAs (IsMonHom (Sheaf.sheafComposeToSheafify (ProEt.topology X)
    (continuousMapRingSheaf X T) (continuousMapRingPresheafToPadicAlgCl X ℓ ψ hψ hE)))

end ToPadicAlgCl

/-- The inclusion `ℚ_ℓ,X ⟶ ℚ̄_ℓ,X`, a morphism of ring objects. -/
noncomputable def padicSheafToPadicAlgClSheaf :
    (sheafCompose (ProEt.topology X) (forget₂ RingCat.{u + 1} Ab.{u + 1})).obj
      (padicSheaf X ℓ) ⟶ padicAlgClSheaf X ℓ :=
  continuousMapRingSheafToPadicAlgClSheaf X ℓ (algebraMap ℚ_[ℓ] (PadicAlgCl ℓ))
    (continuous_algebraMap ℚ_[ℓ] (PadicAlgCl ℓ))
    ⟨⊥, inferInstance, fun t ↦ IntermediateField.algebraMap_mem ⊥ t⟩

instance : IsMonHom (padicSheafToPadicAlgClSheaf X ℓ) :=
  inferInstanceAs (IsMonHom (continuousMapRingSheafToPadicAlgClSheaf X ℓ
    (algebraMap ℚ_[ℓ] (PadicAlgCl ℓ)) (continuous_algebraMap ℚ_[ℓ] (PadicAlgCl ℓ))
    ⟨⊥, inferInstance, fun t ↦ IntermediateField.algebraMap_mem ⊥ t⟩))

section SubfieldToPadicAlgCl

variable (E : Type) [Field E] [Algebra E (PadicAlgCl ℓ)] [Algebra ℚ_[ℓ] E]
  [IsScalarTower ℚ_[ℓ] E (PadicAlgCl ℓ)] [FiniteDimensional ℚ_[ℓ] E]

/-- The image of a finite subextension `E ⊆ ℚ̄_ℓ` of `ℚ_ℓ` is a finite subextension. -/
lemma finiteDimensional_fieldRange_toAlgHom :
    FiniteDimensional ℚ_[ℓ] (IsScalarTower.toAlgHom ℚ_[ℓ] E (PadicAlgCl ℓ)).fieldRange := by
  have h : FiniteDimensional ℚ_[ℓ] (IsScalarTower.toAlgHom ℚ_[ℓ] E (PadicAlgCl ℓ)).range :=
    (AlgEquiv.ofInjectiveField
      (IsScalarTower.toAlgHom ℚ_[ℓ] E (PadicAlgCl ℓ))).toLinearEquiv.finiteDimensional
  rw [← AlgHom.fieldRange_toSubalgebra] at h
  exact h

/-- The inclusion `E_X ⟶ ℚ̄_ℓ,X` for a finite subextension `E ⊆ ℚ̄_ℓ` of `ℚ_ℓ`, a morphism of
ring objects. -/
noncomputable def padicSubfieldSheafToPadicAlgClSheaf :
    (sheafCompose (ProEt.topology X) (forget₂ RingCat.{u + 1} Ab.{u + 1})).obj
      (padicSubfieldSheaf X ℓ E) ⟶ padicAlgClSheaf X ℓ :=
  letI := PadicAlgCl.normedFieldOfAlgebra ℓ E
  continuousMapRingSheafToPadicAlgClSheaf X ℓ (algebraMap E (PadicAlgCl ℓ))
    (continuous_algebraMap_padicAlgCl_of_algebra ℓ E)
    ⟨_, finiteDimensional_fieldRange_toAlgHom ℓ E, fun t ↦ ⟨t, rfl⟩⟩

instance : IsMonHom (padicSubfieldSheafToPadicAlgClSheaf X ℓ E) :=
  letI := PadicAlgCl.normedFieldOfAlgebra ℓ E
  inferInstanceAs (IsMonHom (continuousMapRingSheafToPadicAlgClSheaf X ℓ
    (algebraMap E (PadicAlgCl ℓ)) (continuous_algebraMap_padicAlgCl_of_algebra ℓ E)
    ⟨_, finiteDimensional_fieldRange_toAlgHom ℓ E, fun t ↦ ⟨t, rfl⟩⟩))

end SubfieldToPadicAlgCl

/-! ### `ℚ̄_ℓ,X` as the colimit of the `E_X` -/

/-- The inclusion `E_X ⟶ F_X` for subextensions `E ⊆ F ⊆ ℚ̄_ℓ` of `ℚ_ℓ`, a morphism of sheaves of
rings. -/
noncomputable def padicSubfieldSheafMapOfLE {E F : IntermediateField ℚ_[ℓ] (PadicAlgCl ℓ)}
    (h : E ≤ F) : padicSubfieldSheaf X ℓ E ⟶ padicSubfieldSheaf X ℓ F :=
  letI := PadicAlgCl.normedFieldOfAlgebra ℓ E
  letI := PadicAlgCl.normedFieldOfAlgebra ℓ F
  continuousMapRingSheafMap X (IntermediateField.inclusion h).toRingHom
    (continuous_induced_rng.mpr continuous_induced_dom)

/-- The diagram `E ↦ E_X` of sheaves of rings, indexed by the finite subextensions `E ⊆ ℚ̄_ℓ` of
`ℚ_ℓ` ordered by inclusion. -/
noncomputable def padicSubfieldSheafFunctor :
    PadicAlgCl.FiniteIntermediateField ℓ ⥤ Sheaf (ProEt.topology X) RingCat.{u + 1} where
  obj E := padicSubfieldSheaf X ℓ E.1
  map f := padicSubfieldSheafMapOfLE X ℓ (leOfHom f)
  map_id _ := rfl
  map_comp _ _ := rfl

/-- The cocone of abelian sheaves over the diagram `E ↦ E_X` with vertex `ℚ̄_ℓ,X`, given by the
inclusions `E_X ⟶ ℚ̄_ℓ,X`. -/
noncomputable def padicAlgClSheafCocone :
    Cocone (padicSubfieldSheafFunctor X ℓ ⋙
      sheafCompose (ProEt.topology X) (forget₂ RingCat.{u + 1} Ab.{u + 1})) :=
  Cocone.mk (padicAlgClSheaf X ℓ)
    { app E := padicSubfieldSheafToPadicAlgClSheaf X ℓ E.1
      naturality _ _ f := by
        refine Eq.trans ?_ (Category.comp_id _).symm
        exact Sheaf.sheafCompose_map_comp_sheafComposeToSheafify _ _
          ((padicSubfieldSheafFunctor X ℓ).map f) }

/-- The cocone of abelian presheaves over the diagram `E ↦ C(-, E)` with vertex the presheaf
`U ↦ {f ∈ C(U, ℚ̄_ℓ) | f takes values in a finite subextension}`, whose sheafification is
`padicAlgClSheafCocone`. -/
noncomputable def padicAlgClPresheafCocone :
    Cocone (padicSubfieldSheafFunctor X ℓ ⋙ sheafToPresheaf _ _ ⋙
      (Functor.whiskeringRight _ _ _).obj (forget₂ RingCat.{u + 1} Ab.{u + 1})) :=
  Cocone.mk (padicAlgClRingPresheaf X ℓ ⋙ forget₂ RingCat.{u + 1} Ab.{u + 1})
    { app E := Functor.whiskerRight (letI := PadicAlgCl.normedFieldOfAlgebra ℓ E.1
        continuousMapRingPresheafToPadicAlgCl X ℓ (algebraMap E.1 (PadicAlgCl ℓ))
          (continuous_algebraMap_padicAlgCl_of_algebra ℓ E.1)
          ⟨_, finiteDimensional_fieldRange_toAlgHom ℓ E.1, fun t ↦ ⟨t, rfl⟩⟩) _
      naturality _ _ _ := rfl }

/-- The presheaf `U ↦ {f ∈ C(U, ℚ̄_ℓ) | f takes values in a finite subextension}` is the
colimit of the presheaves `U ↦ C(U, E)`: objectwise, it is the filtered union of the injective
maps `C(U, E) → C(U, ℚ̄_ℓ)`. -/
noncomputable def isColimitPadicAlgClPresheafCocone :
    IsColimit (padicAlgClPresheafCocone X ℓ) := by
  haveI := preservesSmallestFilteredColimits_of_preservesFilteredColimits (forget Ab.{u + 1})
  haveI : ReflectsColimitsOfShape (PadicAlgCl.FiniteIntermediateField ℓ) (forget Ab.{u + 1}) :=
    reflectsColimitsOfShape_of_reflectsIsomorphisms
  refine evaluationJointlyReflectsColimits _ fun U ↦ isColimitOfReflects (forget Ab.{u + 1}) ?_
  refine Types.FilteredColimit.isColimitOf' _ _ ?_ ?_
  · intro x
    obtain ⟨⟨f, E, hE, hf⟩⟩ := x
    let := PadicAlgCl.normedFieldOfAlgebra ℓ E
    refine ⟨⟨E, hE⟩, ULift.up (⟨fun x ↦ ⟨f x, hf x⟩, continuous_induced_rng.mpr f.2⟩ :
      C(U.unop.left, E)), ?_⟩
    rfl
  · intro E x y h
    refine ⟨E, 𝟙 E, ?_⟩
    obtain ⟨x⟩ := x
    obtain ⟨y⟩ := y
    have h' : ∀ t, (x t : PadicAlgCl ℓ) = y t := fun t ↦
      congrArg (fun z : ULift.{u + 1} (PadicAlgCl.finiteIntermediateFieldValued ℓ U.unop.left) ↦
        (z.down : C(U.unop.left, PadicAlgCl ℓ)) t) h
    have : x = y := ContinuousMap.ext fun t ↦ Subtype.val_injective (h' t)
    subst this
    rfl

/-- `ℚ̄_ℓ,X` is the colimit of the abelian sheaves `E_X = C(-, E)` over the finite subextensions
`E ⊆ ℚ̄_ℓ` of `ℚ_ℓ` [Bhatt–Scholze, Section 6.8]: it is the sheafification of the colimit
`padicAlgClPresheafCocone` of the underlying presheaves, sheafification being a left adjoint. -/
noncomputable def isColimitPadicAlgClSheafCocone : IsColimit (padicAlgClSheafCocone X ℓ) := by
  let α : (padicSubfieldSheafFunctor X ℓ ⋙ sheafToPresheaf _ _ ⋙
      (Functor.whiskeringRight _ _ _).obj (forget₂ RingCat.{u + 1} Ab.{u + 1})) ⋙
        presheafToSheaf (ProEt.topology X) Ab.{u + 1} ≅
      padicSubfieldSheafFunctor X ℓ ⋙
        sheafCompose (ProEt.topology X) (forget₂ RingCat.{u + 1} Ab.{u + 1}) :=
    NatIso.ofComponents (fun E ↦ Sheaf.sheafifyRingPresheafIso.{u + 1, u, u + 1} _ _) fun f ↦ by
      simp [Sheaf.sheafCompose_map_eq]
  refine (IsColimit.precomposeHomEquiv α _).1 ?_
  refine IsColimit.ofIsoColimit (isColimitOfPreserves (presheafToSheaf _ Ab.{u + 1})
    (isColimitPadicAlgClPresheafCocone X ℓ)) (Cocone.ext (Iso.refl _) fun E ↦ ?_)
  simp only [Functor.mapCocone_ι_app, Iso.refl_hom, Category.comp_id, Cocone.precompose_obj_ι,
    NatTrans.comp_app]
  exact (Iso.hom_inv_id_assoc _ _).symm

end AlgebraicGeometry.ProEtale
