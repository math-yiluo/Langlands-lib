import Langlands.Representation.Smooth.FiniteLengthGrothendieckIso
import Langlands.Representation.Smooth.Transfer.SubquotientProof
import Langlands.Representation.Smooth.FiniteLengthInductionStatement
import Langlands.Representation.Smooth.Admissibility.FiniteLengthReduction
import Langlands.Representation.Smooth.IrreducibleRealization

/-! Finite-length preservation from exactness and the irreducible case. -/

noncomputable section

open CategoryTheory
open scoped MonoidAlgebra

namespace Langlands.SmoothRep

universe uR uG uV uS uH uW

variable {k : Type uR} [Field k] {G : Type uG} [Group G] [TopologicalSpace G]
  {S : Type uS} [CommRing S] {H : Type uH} [Group H] [TopologicalSpace H]

private theorem finiteLength_middle
    {A B C : SmoothRep.{uS, uH, uW} S H}
    (f : A.representation.IntertwiningMap B.representation)
    (g : B.representation.IntertwiningMap C.representation)
    (h : IsShortExact f g) (hA : A.HasFiniteLength) (hC : C.HasFiniteLength) :
    B.HasFiniteLength := by
  let f' := Representation.IntertwiningMap.equivLinearMapAsModule _ _ f
  let g' := Representation.IntertwiningMap.equivLinearMapAsModule _ _ g
  have hex : LinearMap.range f' = LinearMap.ker g' := by
    ext v
    exact SetLike.ext_iff.mp h.2.2 v
  obtain ⟨hAN, hAA⟩ := isFiniteLength_iff_isNoetherian_isArtinian.mp hA
  obtain ⟨hCN, hCA⟩ := isFiniteLength_iff_isNoetherian_isArtinian.mp hC
  let := hAN
  let := hAA
  let := hCN
  let := hCA
  exact isFiniteLength_iff_isNoetherian_isArtinian.mpr
    ⟨isNoetherian_of_range_eq_ker f' g' hex, isArtinian_of_range_eq_ker f' g' hex⟩

private noncomputable abbrev restrictedModule (M : Type uV) [AddCommGroup M]
    [Module k[G] M] :
    @Module k (RestrictScalars k k[G] M) _ AddCommGroup.toAddCommMonoid :=
  RestrictScalars.module k k[G] M

attribute [local instance] restrictedModule

set_option backward.isDefEq.respectTransparency false in
private noncomputable def moduleIntertwiner
    {M N : Type uV} [AddCommGroup M] [Module k[G] M]
    [AddCommGroup N] [Module k[G] N] (f : M →ₗ[k[G]] N) :
    (Representation.ofModule (k := k) (G := G) M).IntertwiningMap
      (Representation.ofModule (k := k) (G := G) N) where
  toFun := f
  map_add' := f.map_add
  map_smul' c x := f.map_smul (algebraMap k k[G] c) x
  isIntertwining' g := by ext; apply f.map_smul

private noncomputable def moduleRepresentationEquiv
    (M : Type uV) [AddCommGroup M] [Module k[G] M] :
    (Representation.ofModule (k := k) (G := G) M).asModule ≃ₗ[k[G]] M where
  toAddEquiv := (Representation.ofModule M).asModuleEquiv.toAddEquiv.trans
    (RestrictScalars.addEquiv k k[G] M)
  map_smul' := Representation.smul_ofModule_asModule M

private theorem module_image_finiteLength
    (Φ : SmoothRep.{uR, uG, uV} k G ⥤ SmoothRep.{uS, uH, uW} S H)
    (hx : PreservesFiniteLengthShortExact Φ)
    (hirr : ∀ A : SmoothRep.{uR, uG, uV} k G,
      A.IsIrreducible → (Φ.obj A).HasFiniteLength)
    {M : Type uV} [AddCommGroup M] [Module k[G] M]
    (hM : IsFiniteLength k[G] M) :
    ∀ hsmooth : IsSmooth (Representation.ofModule (k := k) (G := G) M),
      (Φ.obj (of _ hsmooth)).HasFiniteLength := by
  induction hM with
  | @of_subsingleton M _ _ _ =>
      intro hsmooth
      let : Subsingleton (RestrictScalars k k[G] M) :=
        (RestrictScalars.addEquiv k k[G] M).injective.subsingleton
      let A := of (Representation.ofModule (k := k) (G := G) M) hsmooth
      have hA : A.HasFiniteLength :=
        (moduleRepresentationEquiv M).symm.isFiniteLength .of_subsingleton
      have hseq : IsShortExact (hom (𝟙 A)) (hom (𝟙 A)) := by
        refine ⟨Function.injective_id, Function.surjective_id, ?_⟩
        ext v
        constructor
        · intro _
          exact Subsingleton.elim _ _
        · intro _
          exact ⟨v, rfl⟩
      have hseq' := hx (𝟙 A) (𝟙 A) hA hA hA hseq
      rw [Φ.map_id] at hseq'
      have hz (v : Φ.obj A) : v = 0 := by
        have hv : v ∈ LinearMap.range (hom (𝟙 (Φ.obj A))).toLinearMap := ⟨v, rfl⟩
        rw [hseq'.2.2] at hv
        exact hv
      let : Subsingleton (Φ.obj A).representation.asModule :=
        ⟨fun x y => (hz x).trans (hz y).symm⟩
      exact IsFiniteLength.of_subsingleton
  | @of_simple_quotient M _ _ N _ hN ih =>
      intro hsmooth
      let i := moduleIntertwiner N.subtype
      let q := moduleIntertwiner N.mkQ
      have hi : Function.Injective i := N.injective_subtype
      have hq : Function.Surjective q := N.mkQ_surjective
      have hNs := isSmooth_of_injective i hi hsmooth
      have hQs := isSmooth_of_surjective q hq hsmooth
      let A := of (Representation.ofModule (k := k) (G := G) N) hNs
      let B := of (Representation.ofModule (k := k) (G := G) M) hsmooth
      let C := of (Representation.ofModule (k := k) (G := G) (M ⧸ N)) hQs
      have hA : A.HasFiniteLength := (moduleRepresentationEquiv N).symm.isFiniteLength hN
      have hB : B.HasFiniteLength :=
        (moduleRepresentationEquiv M).symm.isFiniteLength (.of_simple_quotient hN)
      have hCirr : C.IsIrreducible :=
        (Representation.isSimpleModule_iff_irreducible_ofModule (M ⧸ N)).mp inferInstance
      have hC : C.HasFiniteLength := hasFiniteLength_of_isIrreducible hCirr
      have hseq : IsShortExact (A := A) (B := B) (C := C) i q := by
        refine ⟨hi, hq, ?_⟩
        ext v
        constructor
        · rintro ⟨w, rfl⟩
          let x : N := RestrictScalars.addEquiv k k[G] N w
          change N.mkQ (x : M) = 0
          exact (Submodule.Quotient.mk_eq_zero N).mpr x.property
        · intro hv
          let x : M := RestrictScalars.addEquiv k k[G] M v
          have hx : x ∈ N := (Submodule.Quotient.mk_eq_zero N).mp hv
          exact ⟨(RestrictScalars.addEquiv k k[G] N).symm ⟨x, hx⟩, rfl⟩
      exact finiteLength_middle
        (hom (Φ.map (ofHom (A := A) (B := B) i)))
        (hom (Φ.map (ofHom (A := B) (B := C) q)))
        (hx (ofHom (A := A) (B := B) i) (ofHom (A := B) (B := C) q)
          hA hB hC hseq) (ih hNs) (hirr C hCirr)

/-- Exactness on finite-length terms and the irreducible case suffice to
preserve every finite-length smooth representation. -/
theorem preservesFiniteLength_of_irreducibles
    (Φ : SmoothRep.{uR, uG, uV} k G ⥤ SmoothRep.{uS, uH, uW} S H)
    (hx : PreservesFiniteLengthShortExact Φ)
    (hirr : ∀ A : SmoothRep.{uR, uG, uV} k G,
      A.IsIrreducible → (Φ.obj A).HasFiniteLength) :
    PreservesFiniteLength Φ := by
  intro A hA
  let f := Langlands.representationToModuleIntertwiner A.representation
  have hf : Function.Bijective f :=
    (RestrictScalars.addEquiv k k[G] A.representation.asModule).symm.bijective.comp
      A.representation.asModuleEquiv.symm.bijective
  have hsmooth := isSmooth_of_surjective f hf.2 A.isSmooth
  let B := of (Representation.ofModule (k := k) (G := G) A.representation.asModule) hsmooth
  have e : A ≅ B := mkIso (f.ofBijective hf)
  exact hasFiniteLength_of_iso (Φ.mapIso e.symm)
    (module_image_finiteLength Φ hx hirr hA hsmooth)

/-- The closed generic finite-length reduction, at six independent universes. -/
theorem finiteLengthInduction :
    FiniteLengthInductionStatement.{uR, uG, uV, uS, uH, uW} := by
  intro k _ G _ _ S _ H _ _ Φ hx hirr
  exact preservesFiniteLength_of_irreducibles Φ hx hirr

end Langlands.SmoothRep
