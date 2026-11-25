/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import WeilConjectures.CategoryTheory.RingObjects.Condensed.ContinuousMap
public import WeilConjectures.CategoryTheory.RingObjects.EllAdic

/-!

# The condensed coefficient rings `ℤ_ℓ`, `ℚ_ℓ`, `𝒪_E`, `E` and `ℚ̄_ℓ`

Fix a prime `ℓ`. The four *topological* `ℓ`-adic coefficient rings are defined as condensed
rings by their sections on profinite sets, following Section 3 of
`WeilConjectures/RefactorInstruction.tex`:
```
ℤ̲_ℓ(S) := C(S, ℤ_ℓ),   ℚ̲_ℓ(S) := C(S, ℚ_ℓ),   𝒪̲_E(S) := C(S, 𝒪_E),   E̲(S) := C(S, E),
```
with restriction by precomposition and the pointwise ring operations: each is
`Profinite.continuousMapRingSheaf` of the corresponding topological ring. Here `E` is a subfield
of `ℚ̄_ℓ = PadicAlgCl ℓ`, given by an embedding `E → ℚ̄_ℓ`, with the topology restricted from
`ℚ̄_ℓ` (`PadicAlgCl.normedFieldOfAlgebra`), and `𝒪_E = PadicAlgCl.integers ℓ E` is its ring of
integers.

The familiar descriptions `ℤ̲_ℓ ≅ lim_n ℤ/ℓⁿ`, `ℚ̲_ℓ ≅ ℤ̲_ℓ[1/ℓ]`, `𝒪̲_E ≅ lim_n 𝒪_E/ϖⁿ` and
`E̲ ≅ 𝒪̲_E[1/ϖ]` are *not* definitions; they are comparison isomorphisms, to be proved later.

The condensed `ℚ̄_ℓ` is not of the form `C(-, T)`. Following Definition 3.6 of the notes, a
section over a profinite set `S` is a continuous map `S → E` into a finite subextension
`E ⊆ ℚ̄_ℓ` of `ℚ_ℓ`, regarded in `ℚ̄_ℓ`: the condensed ring `ℚ̲̄_ℓ` is the subsheaf of
`C(-, ℚ̄_ℓ)` of the maps with values in a finite subextension
(`Profinite.padicAlgClCondensedRing`). The sheaf condition is checked directly: a covering is
refined by a finite jointly surjective family, and finitely many finite subextensions have a
finite compositum. It is *not* `C(-, ℚ̄_ℓ)` for the valuation topology, which has more sections:
a sequence of elements of unbounded degree converging to `0` gives a continuous map on a
convergent sequence that takes values in no finite subextension.

The inclusions `ℤ_ℓ → ℚ_ℓ → E`, `ℤ_ℓ → 𝒪_E → E` are continuous ring homomorphisms, so
postcomposition with them gives morphisms of condensed rings.

## Main definitions

* `Profinite.padicIntCondensedRing`, `Profinite.padicCondensedRing`: the condensed rings
  `ℤ̲_ℓ` and `ℚ̲_ℓ`.
* `Profinite.padicSubfieldCondensedRing`, `Profinite.padicIntegersCondensedRing`: the condensed
  rings `E̲` and `𝒪̲_E`, and `Profinite.padicIntegersRingObj`: the ring object of condensed
  abelian groups underlying `𝒪̲_E`.
* `Profinite.padicIntCondensedRingToPadicCondensedRing`,
  `Profinite.padicCondensedRingToPadicSubfieldCondensedRing`,
  `Profinite.padicIntegersCondensedRingToPadicSubfieldCondensedRing` and
  `Profinite.padicIntCondensedRingToPadicIntegersCondensedRing`: the inclusions, as morphisms of
  condensed rings.
* `Profinite.padicAlgClCondensedRing`: the condensed ring `ℚ̲̄_ℓ`, and
  `Profinite.padicAlgClRingObj`: the underlying ring object of condensed abelian groups.

-/

@[expose] public section

universe u

open CategoryTheory

namespace Profinite

open AlgebraicGeometry.ProEtale

variable (ℓ : ℕ) [Fact ℓ.Prime]

/-! ### `ℤ_ℓ` and `ℚ_ℓ` -/

/-- The condensed ring `ℤ̲_ℓ`, with sections `ℤ̲_ℓ(S) = C(S, ℤ_ℓ)` for the `ℓ`-adic topology. -/
noncomputable abbrev padicIntCondensedRing :
    Sheaf (coherentTopology Profinite.{u}) RingCat.{u + 1} :=
  continuousMapRingSheaf ℤ_[ℓ]

/-- The condensed ring `ℚ̲_ℓ`, with sections `ℚ̲_ℓ(S) = C(S, ℚ_ℓ)` for the `ℓ`-adic topology. -/
noncomputable abbrev padicCondensedRing :
    Sheaf (coherentTopology Profinite.{u}) RingCat.{u + 1} :=
  continuousMapRingSheaf ℚ_[ℓ]

/-- The inclusion `ℤ̲_ℓ ⟶ ℚ̲_ℓ`, a morphism of condensed rings. -/
noncomputable def padicIntCondensedRingToPadicCondensedRing :
    padicIntCondensedRing.{u} ℓ ⟶ padicCondensedRing ℓ :=
  continuousMapRingSheafMap PadicInt.Coe.ringHom continuous_subtype_val

/-! ### Subfields `E` of `ℚ̄_ℓ` -/

section Subfield

variable (E : Type) [Field E] [Algebra E (PadicAlgCl ℓ)]

/-- The condensed ring `E̲`, for a subfield `E` of `ℚ̄_ℓ` given by an embedding `E → ℚ̄_ℓ`, with
sections `E̲(S) = C(S, E)` for the topology of `E` restricted from `ℚ̄_ℓ`. -/
noncomputable abbrev padicSubfieldCondensedRing :
    Sheaf (coherentTopology Profinite.{u}) RingCat.{u + 1} :=
  letI := PadicAlgCl.normedFieldOfAlgebra ℓ E
  continuousMapRingSheaf E

variable [Algebra ℚ_[ℓ] E] [IsScalarTower ℚ_[ℓ] E (PadicAlgCl ℓ)]

/-- The inclusion `ℚ̲_ℓ ⟶ E̲`, a morphism of condensed rings. -/
noncomputable def padicCondensedRingToPadicSubfieldCondensedRing :
    padicCondensedRing.{u} ℓ ⟶ padicSubfieldCondensedRing ℓ E :=
  letI := PadicAlgCl.normedFieldOfAlgebra ℓ E
  continuousMapRingSheafMap (algebraMap ℚ_[ℓ] E) (continuous_algebraMap_padic_of_algebra ℓ E)

end Subfield

/-! ### The rings of integers `𝒪_E` -/

section Integers

variable (E : Type) [Field E] [Algebra E (PadicAlgCl ℓ)]

/-- The condensed ring `𝒪̲_E`, for a subfield `E` of `ℚ̄_ℓ` given by an embedding `E → ℚ̄_ℓ`,
with sections `𝒪̲_E(S) = C(S, 𝒪_E)` into the ring of integers `𝒪_E = PadicAlgCl.integers ℓ E`,
for the topology restricted from `ℚ̄_ℓ`. -/
noncomputable abbrev padicIntegersCondensedRing :
    Sheaf (coherentTopology Profinite.{u}) RingCat.{u + 1} :=
  letI := PadicAlgCl.normedFieldOfAlgebra ℓ E
  continuousMapRingSheaf (PadicAlgCl.integers ℓ E)

/-- The inclusion `𝒪̲_E ⟶ E̲`, a morphism of condensed rings. -/
noncomputable def padicIntegersCondensedRingToPadicSubfieldCondensedRing :
    padicIntegersCondensedRing.{u} ℓ E ⟶ padicSubfieldCondensedRing ℓ E :=
  letI := PadicAlgCl.normedFieldOfAlgebra ℓ E
  continuousMapRingSheafMap (PadicAlgCl.integers ℓ E).subtype continuous_subtype_val

/-- The condensed ring `𝒪̲_E` as a ring object of condensed abelian groups: the abelian sheaf
underlying `padicIntegersCondensedRing ℓ E`, with the ring object structure
`CategoryTheory.Sheaf.monObj_sheafCompose_obj`. -/
noncomputable abbrev padicIntegersRingObj : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1} :=
  (sheafCompose (coherentTopology Profinite.{u}) (forget₂ RingCat.{u + 1} Ab.{u + 1})).obj
    (padicIntegersCondensedRing ℓ E)

/-- The condensed ring `𝒪̲_E` is a commutative ring object of condensed abelian groups. -/
instance isCommMonObj_padicIntegersRingObj : IsCommMonObj (padicIntegersRingObj.{u} ℓ E) :=
  letI := PadicAlgCl.normedFieldOfAlgebra ℓ E
  isCommMonObj_continuousMapRingObj (PadicAlgCl.integers ℓ E)

variable [Algebra ℚ_[ℓ] E] [IsScalarTower ℚ_[ℓ] E (PadicAlgCl ℓ)]

/-- The inclusion `ℤ̲_ℓ ⟶ 𝒪̲_E`, a morphism of condensed rings. -/
noncomputable def padicIntCondensedRingToPadicIntegersCondensedRing :
    padicIntCondensedRing.{u} ℓ ⟶ padicIntegersCondensedRing ℓ E :=
  letI := PadicAlgCl.normedFieldOfAlgebra ℓ E
  continuousMapRingSheafMap (padicIntToIntegers ℓ E) (continuous_padicIntToIntegers ℓ E)

end Integers

/-! ### `ℚ̄_ℓ` -/

section PadicAlgCl

/-- The subfunctor of `S ↦ C(S, ℚ̄_ℓ)` on profinite sets of the continuous maps with values in a
finite subextension `E ⊆ ℚ̄_ℓ` of `ℚ_ℓ`: a section is a continuous map into one finite local
field `E`, regarded in `ℚ̄_ℓ`. -/
def padicAlgClSubfunctor :
    Subfunctor (ContinuousMap.yonedaPresheaf Profinite.toTopCat.{u} (PadicAlgCl ℓ)) where
  obj S := {a | a ∈ PadicAlgCl.finiteIntermediateFieldValued ℓ S.unop}
  map {S S'} u a ha := by
    obtain ⟨E, hE, h⟩ := ha
    exact ⟨E, hE, fun x ↦ h _⟩

/-- The sections with values in a finite subextension form a sheaf for the coherent topology:
a covering is refined by a finite jointly surjective family `{Sᵢ ⟶ S}`, and if `a ∘ πᵢ` takes
values in the finite subextension `Eᵢ` for each `i`, then `a` takes values in their compositum,
which is again finite. -/
lemma isSheaf_padicAlgClSubfunctor :
    Presieve.IsSheaf (coherentTopology Profinite.{u}) (padicAlgClSubfunctor.{u} ℓ).toFunctor := by
  rw [Subfunctor.isSheaf_iff _
    (h := (isSheaf_iff_isSheaf_of_type _ _).mp (isSheaf_yonedaPresheaf (PadicAlgCl ℓ)))]
  intro S a ha
  obtain ⟨α, _, Y, π, hπ, hmem⟩ := (coherentTopology.mem_sieves_iff_hasEffectiveEpiFamily _).mp ha
  choose E hE h using hmem
  have hsurj : ∀ b : S.unop, ∃ (i : α) (y : Y i), π i y = b :=
    ((Profinite.effectiveEpiFamily_tfae Y π).out 1 3).mp hπ
  refine ⟨⨆ i, E i, inferInstance, fun x ↦ ?_⟩
  obtain ⟨i, y, rfl⟩ := hsurj x
  exact (le_iSup E i) (h i y)

/-- The presheaf of rings `S ↦ {a ∈ C(S, ℚ̄_ℓ) | a takes values in a finite subextension}` on
profinite sets, lifted to `Type (u + 1)`. -/
noncomputable def padicAlgClRingPresheaf : Profinite.{u}ᵒᵖ ⥤ RingCat.{u + 1} where
  obj S := RingCat.of (ULift.{u + 1} (PadicAlgCl.finiteIntermediateFieldValued ℓ S.unop))
  map u := RingCat.ofHom
    (ULift.ringEquiv.symm.toRingHom.comp
      (((((ContinuousMap.compRightAlgHom ℤ (PadicAlgCl ℓ) u.unop.hom.hom).toRingHom).comp
          (PadicAlgCl.finiteIntermediateFieldValued ℓ _).subtype).codRestrict
          (PadicAlgCl.finiteIntermediateFieldValued ℓ _) (fun a ↦ by
            obtain ⟨E, hE, h⟩ := a.2
            exact ⟨E, hE, fun x ↦ h _⟩)).comp ULift.ringEquiv.toRingHom))
  map_id _ := rfl
  map_comp _ _ := rfl

/-- The presheaf of types underlying `padicAlgClRingPresheaf ℓ` is the subfunctor
`padicAlgClSubfunctor ℓ`, lifted by one universe. -/
noncomputable def padicAlgClRingPresheafForgetIso :
    padicAlgClRingPresheaf.{u} ℓ ⋙ forget RingCat.{u + 1} ≅
      (padicAlgClSubfunctor.{u} ℓ).toFunctor ⋙ uliftFunctor.{u + 1} :=
  NatIso.ofComponents (fun _ ↦ Iso.refl _) (fun _ ↦ rfl)

/-- The presheaf of rings of sections with values in a finite subextension is a sheaf. -/
lemma isSheaf_padicAlgClRingPresheaf :
    Presheaf.IsSheaf (coherentTopology Profinite.{u}) (padicAlgClRingPresheaf ℓ) := by
  rw [Presheaf.isSheaf_iff_isSheaf_forget _ _ (forget RingCat.{u + 1}),
    Presheaf.isSheaf_of_iso_iff (padicAlgClRingPresheafForgetIso ℓ),
    isSheaf_iff_isSheaf_of_type, Presieve.isSheaf_comp_uliftFunctor_iff]
  exact isSheaf_padicAlgClSubfunctor ℓ

/-- The condensed ring `ℚ̲̄_ℓ`, following Definition 3.6 of
`WeilConjectures/RefactorInstruction.tex`: a section over a profinite set `S` is a continuous map
`S → E` into a finite subextension `E ⊆ ℚ̄_ℓ` of `ℚ_ℓ`, regarded in `ℚ̄_ℓ`, so that two such
maps are identified when they agree pointwise in `ℚ̄_ℓ`. Restriction is precomposition and the
ring operations are computed in a common finite subextension. It is *not* `C(-, ℚ̄_ℓ)` for the
valuation topology of `ℚ̄_ℓ`, which has more sections. -/
noncomputable def padicAlgClCondensedRing :
    Sheaf (coherentTopology Profinite.{u}) RingCat.{u + 1} :=
  ⟨padicAlgClRingPresheaf ℓ, isSheaf_padicAlgClRingPresheaf ℓ⟩

/-- The condensed ring `ℚ̲̄_ℓ` as a ring object of condensed abelian groups: the abelian sheaf
underlying `padicAlgClCondensedRing ℓ`, with the ring object structure
`CategoryTheory.Sheaf.monObj_sheafCompose_obj`. -/
noncomputable abbrev padicAlgClRingObj : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1} :=
  (sheafCompose (coherentTopology Profinite.{u}) (forget₂ RingCat.{u + 1} Ab.{u + 1})).obj
    (padicAlgClCondensedRing ℓ)

/-- The condensed ring `ℚ̲̄_ℓ` is a commutative ring object of condensed abelian groups. -/
instance isCommMonObj_padicAlgClRingObj : IsCommMonObj (padicAlgClRingObj.{u} ℓ) :=
  Sheaf.isCommMonObj_sheafCompose_obj (coherentTopology Profinite.{u})
    (padicAlgClCondensedRing ℓ) fun S
      (a b : ULift.{u + 1} (PadicAlgCl.finiteIntermediateFieldValued ℓ S.unop)) ↦ mul_comm a b

end PadicAlgCl

end Profinite
