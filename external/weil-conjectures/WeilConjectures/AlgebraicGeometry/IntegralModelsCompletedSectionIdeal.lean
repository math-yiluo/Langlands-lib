/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.IntegralModelsCompletedSectionRing
import all WeilConjectures.AlgebraicGeometry.CompletedConstantAlgebraFlatQuotients
import all WeilConjectures.AlgebraicGeometry.ConstantCompletionCore
import all WeilConjectures.AlgebraicGeometry.IntegralConstantCompletion
import WeilConjectures.AlgebraicGeometry.IntegralModelsResidueIdealComparison

/-! # The first completed residue ideal in section coordinates

Source: Stacks Tags 093M, 099C and 099L.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale.IntegralModelsStacks
attribute [local irreducible] upperStarFromPoint

private theorem kernel_sections {C : Type u} [SmallCategory C]
    {J : GrothendieckTopology C} {R S : Sheaf J CommRingCat.{u}}
    (q : R ⟶ S) (U : C) :
    (ConstantCompletion.kernelIdeal q).sections U = RingHom.ker (q.hom.app (op U)).hom :=
  (ConstantCompletion.kernelIdeal_existsUnique q).exists.choose_spec U

private theorem kernel_mem_transport {C : Type u} [SmallCategory C]
    {J : GrothendieckTopology C} {R S R₀ S₀ : Sheaf J CommRingCat.{u}}
    (q : R ⟶ S) (q₀ : R₀ ⟶ S₀) (α : R ≅ R₀) (γ : S ≅ S₀)
    (hq : q ≫ γ.hom = α.hom ≫ q₀) (U : C) (a : R.obj.obj (op U)) :
    a ∈ (ConstantCompletion.kernelIdeal q).sections U ↔
      α.hom.hom.app (op U) a ∈ (ConstantCompletion.kernelIdeal q₀).sections U := by
  rw [kernel_sections, kernel_sections]
  change q.hom.app (op U) a = 0 ↔ q₀.hom.app (op U) (α.hom.hom.app (op U) a) = 0
  have hc := congrArg (fun f ↦ f.hom.app (op U) a) hq
  change γ.hom.hom.app (op U) (q.hom.app (op U) a) =
    q₀.hom.app (op U) (α.hom.hom.app (op U) a) at hc
  rw [← hc, ← map_zero (γ.hom.hom.app (op U)).hom]
  exact ((((sheafToPresheaf J CommRingCat).mapIso γ).app
    (op U)).commRingCatIsoToRingEquiv.injective).eq_iff.symm

private theorem constant_reduced {C : Type u} [SmallCategory C]
    (J : GrothendieckTopology C) (A : Type u) [CommRing A] [_root_.IsReduced A]
    (U : Cᵒᵖ) : _root_.IsReduced ((ConstantCompletion.constant J A).obj.obj U) := by
  let R := ConstantCompletion.constant J A
  let η := toSheafify J ((Functor.const Cᵒᵖ).obj (CommRingCat.of A))
  constructor
  intro x hx
  obtain ⟨n, hn⟩ := hx
  apply R.isSeparated U.unop (Presheaf.imageSieve η x)
    (Presheaf.imageSieve_mem J η x)
  intro V g hg
  obtain ⟨a, ha⟩ := hg
  change A at a
  change R.obj.map g.op x = R.obj.map g.op 0
  change η.app (op V) a = R.obj.map g.op x at ha
  rw [map_zero, ← ha]
  have hp : η.app (op V) (a ^ n) = η.app (op V) 0 := by
    have ha' : (η.app (op V)).hom a = (R.obj.map g.op).hom x := ha
    have hpow : ((R.obj.map g.op).hom x) ^ n = 0 := by
      rw [← map_pow, hn, map_zero]
    calc
      η.app (op V) (a ^ n) = (η.app (op V) a) ^ n := map_pow _ _ _
      _ = 0 := by rw [ha']; exact hpow
      _ = η.app (op V) 0 := (map_zero _).symm
  have hcov := Presheaf.equalizerSieve_mem J η (a ^ n) 0 hp
  apply R.isSeparated V (Presheaf.equalizerSieve
    (F := (Functor.const Cᵒᵖ).obj (CommRingCat.of A)) (X := op V) (a ^ n) (0 : A)) hcov
  intro W f hf
  change a ^ n = 0 at hf
  have hzero : a = 0 := _root_.IsReduced.eq_zero a ⟨n, hf⟩
  simp only [hzero, map_zero]

private theorem integers_radical (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] :
    IntegralConstantCompletion.ideal l E =
      (Ideal.span {(l : IntegralConstantCompletion.integers l E)}).radical := by
  let A := Padic.coefficientExtensionIntegers l E
  let m := Padic.coefficientExtensionMaximalIdeal l E
  have hd := (Padic.coefficientExtensionIntegers_dvr l E).choose_spec
  have hgen : Ideal.span {Padic.coefficientExtensionUniformizer l E} = m :=
    hd.2.2.2.2.2.2.2.2.2.2.2.2.2.1.choose_spec
  have hm : m.IsMaximal := hd.2.2.2.2.1
  have hp : ∀ P : Ideal A, P.IsPrime ∧ P ≠ ⊥ ↔ P = m :=
    hd.2.2.2.2.2.2.2.2.2.2.1
  have hl : (l : A) ∈ m := by
    apply (hd.2.1 _).mpr
    change spectralNorm (Padic l) E (l : E) < 1
    rw [← map_natCast (algebraMap (Padic l) E), spectralNorm_extends]
    exact Padic.norm_p_lt_one
  have hl0 : (l : A) ≠ 0 := by
    intro hz
    have hzE : (l : E) = 0 := congrArg (fun a : A ↦ (a : E)) hz
    have hzP : (l : Padic l) = 0 :=
      (algebraMap (Padic l) E).injective (by simpa using hzE)
    have hzN : l = 0 := by exact_mod_cast hzP
    exact (Fact.out : l.Prime).ne_zero hzN
  have he : (Ideal.span {(l : A)}).radical = m := by
    rw [Ideal.radical_eq_sInf]
    apply le_antisymm
    · exact sInf_le ⟨(Ideal.span_singleton_le_iff_mem _).mpr hl, hm.isPrime⟩
    · apply le_sInf
      intro P hP
      have hP0 : P ≠ ⊥ := by
        intro hz
        have hx := hP.1 (Ideal.subset_span (Set.mem_singleton (l : A)))
        rw [hz, Ideal.mem_bot] at hx
        exact hl0 hx
      exact ((hp P).mp ⟨hP.2, hP0⟩).symm.le
  let e : IntegralConstantCompletion.integers l E ≃+* A := ULift.ringEquiv
  have hI : Ideal.map e.toRingHom (IntegralConstantCompletion.ideal l E) = m := by
    rw [IntegralConstantCompletion.ideal, Ideal.map_span, Set.image_singleton]
    exact hgen
  have hker : RingHom.ker e.toRingHom ≤
      Ideal.span {(l : IntegralConstantCompletion.integers l E)} := by
    rw [(RingHom.injective_iff_ker_eq_bot e.toRingHom).mp e.injective]
    exact bot_le
  have hmap : Ideal.map e.toRingHom
      (Ideal.span {(l : IntegralConstantCompletion.integers l E)}).radical = m := by
    rw [Ideal.map_radical_of_surjective e.surjective hker,
      Ideal.map_span, Set.image_singleton, map_natCast, he]
  have hh := congrArg (Ideal.comap e.toRingHom) (hI.trans hmap.symm)
  simpa only [Ideal.comap_map_of_bijective e.toRingHom e.bijective] using hh

private theorem kernel_radical_nat {A B S : Type u}
    [CommRing A] [CommRing B] [CommRing S] [_root_.IsReduced S]
    (l : ℕ) (I : Ideal A) (f : A →+* B) (q : B →+* S)
    (hI : I = (Ideal.span {(l : A)}).radical)
    (hk : RingHom.ker q = Ideal.map f I) :
    RingHom.ker q = (Ideal.span {(l : B)}).radical := by
  apply le_antisymm
  · rw [hk, hI]
    simpa only [Ideal.map_span, Set.image_singleton, map_natCast] using
      (Ideal.map_radical_le (f := f) (I := Ideal.span {(l : A)}))
  · have hl : (l : B) ∈ RingHom.ker q := by
      rw [hk, ← map_natCast f l]
      apply Ideal.mem_map_of_mem
      rw [hI]
      exact Ideal.le_radical (Ideal.subset_span (Set.mem_singleton _))
    have hle : Ideal.span {(l : B)} ≤ RingHom.ker q :=
      (Ideal.span_singleton_le_iff_mem _).mpr hl
    intro x hx
    obtain ⟨n, hn⟩ := hx
    have hz : q x ^ n = 0 := by
      rw [← map_pow]
      exact hle hn
    exact _root_.IsReduced.eq_zero _ ⟨n, hz⟩

private theorem integers_prime (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] :
    (IntegralConstantCompletion.ideal l E).IsPrime := by
  have hd := (Padic.coefficientExtensionIntegers_dvr l E).choose_spec
  have hgen : Ideal.span {Padic.coefficientExtensionUniformizer l E} =
      Padic.coefficientExtensionMaximalIdeal l E :=
    hd.2.2.2.2.2.2.2.2.2.2.2.2.2.1.choose_spec
  let e : IntegralConstantCompletion.integers l E ≃+*
      Padic.coefficientExtensionIntegers l E := ULift.ringEquiv
  have hm : (Padic.coefficientExtensionMaximalIdeal l E).IsPrime :=
    hd.2.2.2.2.1.isPrime
  have he : Ideal.map e.toRingHom (IntegralConstantCompletion.ideal l E) =
      Padic.coefficientExtensionMaximalIdeal l E := by
    rw [IntegralConstantCompletion.ideal, Ideal.map_span, Set.image_singleton]
    exact hgen
  have h := hm.comap e.toRingHom
  rw [← he, Ideal.comap_map_of_bijective e.toRingHom e.bijective] at h
  exact h

private theorem first_kernel_radical {C : Type u} [SmallCategory C]
    (J : GrothendieckTopology C) (A : Type u) [CommRing A] [IsNoetherianRing A]
    (I : Ideal A) [I.IsPrime] (l : ℕ)
    (hI : I = (Ideal.span {(l : A)}).radical) (U : C) :
    (ConstantCompletion.kernelIdeal (ConstantCompletion.projection J A I 0)).sections U =
      (Ideal.span {(l : (ConstantCompletion.completed J A I).obj.obj (op U))}).radical := by
  let B := ConstantCompletion.completed J A I
  let f : A →+* B.obj.obj (op U) :=
    ((ConstantCompletion.coefficientMap J A I).hom.app (op U)).hom.comp
      ((toSheafify J ((Functor.const Cᵒᵖ).obj (CommRingCat.of A))).app (op U)).hom
  let : _root_.IsReduced ((ConstantCompletion.finite J A I 0).obj.obj (op U)) := by
    change _root_.IsReduced ((ConstantCompletion.constant J (A ⧸ I ^ (0 + 1))).obj.obj
      (op U))
    have hpow : I ^ (0 + 1) = I := by rw [Nat.zero_add, pow_one]
    rw [hpow]
    exact constant_reduced J (A ⧸ I) (op U)
  rw [kernel_sections]
  apply kernel_radical_nat l I f _ hI
  rw [((ConstantCompletion.flat_and_quotients J A I).2.1 0 U).2, pow_one]
  change Ideal.span (Set.range (fun a : I ↦ f a)) = Ideal.span (f '' (I : Set A))
  congr 1
  ext b
  exact ⟨fun ⟨a, ha⟩ ↦ ⟨a, a.property, ha⟩,
    fun ⟨a, ha, hab⟩ ↦ ⟨⟨a, ha⟩, hab⟩⟩

private theorem comap_radical_nat {A B : Type u} [CommRing A] [CommRing B]
    (e : A ≃+* B) (l : ℕ) :
    Ideal.comap e.toRingHom (Ideal.span {(l : B)}).radical =
      (Ideal.span {(l : A)}).radical := by
  rw [Ideal.comap_radical]
  congr 1
  have h : Ideal.map e.toRingHom (Ideal.span {(l : A)}) = Ideal.span {(l : B)} := by
    rw [Ideal.map_span, Set.image_singleton, map_natCast]
  rw [← h, Ideal.comap_map_of_bijective e.toRingHom e.bijective]

private theorem kernel_radical_transport {C : Type u} [SmallCategory C]
    {J : GrothendieckTopology C} {R S R₀ S₀ : Sheaf J CommRingCat.{u}}
    (q : R ⟶ S) (q₀ : R₀ ⟶ S₀) (α : R ≅ R₀) (γ : S ≅ S₀)
    (hq : q ≫ γ.hom = α.hom ≫ q₀) (l : ℕ)
    (hk : ∀ U, (ConstantCompletion.kernelIdeal q₀).sections U =
      (Ideal.span {(l : R₀.obj.obj (op U))}).radical) (U : C) :
    (ConstantCompletion.kernelIdeal q).sections U =
      (Ideal.span {(l : R.obj.obj (op U))}).radical := by
  let e := (((sheafToPresheaf J CommRingCat).mapIso α).app (op U)).commRingCatIsoToRingEquiv
  have h := comap_radical_nat e l
  ext x
  rw [kernel_mem_transport q q₀ α γ hq, hk U]
  exact SetLike.ext_iff.mp h x

private theorem first_kernel_small (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (X : Scheme.{u}) (U : Scheme.coefficientProEtaleSiteModel.{u, u} X) :
    (ConstantCompletion.kernelIdeal ((Scheme.sfbModelRings X).map
      (limit.π (Scheme.adicLisseRingSystem X (IntegralConstantCompletion.ideal l E))
        (op 0)))).sections U =
      (Ideal.span {(l : ((Scheme.sfbModelRings X).obj
        (Scheme.adicLisseCompletedRing X (IntegralConstantCompletion.ideal l E))).obj.obj
          (op U))}).radical := by
  let A := IntegralConstantCompletion.integers l E
  let I := IntegralConstantCompletion.ideal l E
  let J := Scheme.coefficientProEtaleModelTopology.{u, u} X
  let F := Scheme.CompletedConstantAlgebra.pushRing X
  let : IsNoetherianRing A := IntegralConstantCompletion.integers_noetherian l E
  let : I.IsPrime := integers_prime l E
  exact kernel_radical_transport _ (ConstantCompletion.projection J A I 0)
    (Scheme.CompletedConstantAlgebra.completionIso X I)
    ((Scheme.CompletedConstantAlgebra.constantsIso X).app (CommRingCat.of (A ⧸ I ^ (0 + 1))))
    (Scheme.CompletedConstantAlgebra.completionIso_projection X I 0).symm l
    (first_kernel_radical J A I l (integers_radical l E)) U

private theorem extension_radical_iso {C : Type u} [SmallCategory C]
    {J : GrothendieckTopology C} {R B : Sheaf J CommRingCat.{u}}
    (e : R ≅ B) (K : RingedSiteIdeal R) (L : RingedSiteIdeal B) (l : ℕ)
    (hK : ∀ U, K.sections U = (Ideal.span {(l : R.obj.obj (op U))}).radical)
    (hL : ∀ U, L.sections U = (Ideal.span {(l : B.obj.obj (op U))}).radical) :
    K.extension e.hom = L := by
  apply ConstantCompletion.extension_eq_of_span
  intro U
  have he : Function.Bijective (e.hom.hom.app (op U)).hom :=
    (((sheafToPresheaf J CommRingCat).mapIso e).app (op U)).commRingCatIsoToRingEquiv.bijective
  have himage : Set.range (fun a : K.sections U ↦ e.hom.hom.app (op U) a) =
      (e.hom.hom.app (op U)).hom '' (K.sections U : Set (R.obj.obj (op U))) := by
    ext x
    exact ⟨fun ⟨a, ha⟩ ↦ ⟨a, a.property, ha⟩,
      fun ⟨a, ha, hab⟩ ↦ ⟨⟨a, ha⟩, hab⟩⟩
  rw [himage]
  change L.sections U = Ideal.map (e.hom.hom.app (op U)).hom (K.sections U)
  rw [hK, hL, Ideal.map_radical_of_surjective he.2
    (by rw [(RingHom.injective_iff_ker_eq_bot _).mp he.1]; exact bot_le),
    Ideal.map_span, Set.image_singleton, map_natCast]

/-- The normalized coefficient isomorphism carries the first completed residue ideal
onto the extension of the discrete residue kernel. This assertion concerns only ideals
of ordinary ring sheaves, independently of complexes and completeness predicates.

Source: blueprint integral-models proof (1), coefficient identification; Stacks Tags
093M, 099C and 099L.
(auxiliary; not a blueprint node).

Proof: the maximal ideal of O_E is the radical of (l): it contains the nonzero
rational prime, and it is the unique nonzero prime ideal of this DVR. Constant
sheafification of a reduced ring has reduced section rings, by local lifting to the
constant presheaf and local injectivity of the sheafification unit. Thus the first
completed residue kernel, whose generators are given by flat_and_quotients, is
sectionwise the radical of (l). A scalar-compatible completion comparison similarly
identifies the extension of the discrete residue kernel with this radical in the
continuous ring. Every ring isomorphism preserves (l) and its radical. Apply this
to completedSectionIso and use the local characterization of ideal extension.
No compatibility of completedSectionIso with a finite projection is needed. The
argument includes empty schemes and empty site objects. -/
theorem completedSectionIdeal (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (X : Scheme.{u}) [IsNoetherian X] :
    (ConstantCompletion.kernelIdeal
      ((Scheme.sfbModelRings X).map
        (limit.π (Scheme.adicLisseRingSystem X (IntegralConstantCompletion.ideal l E))
          (op 0)))).extension
        ((Scheme.sfbModelRings X).map (completedSectionIso l E X).hom) =
      (ConstantCompletion.kernelIdeal (smallMap X (residueMap l E X))).extension
        (smallMap X (scalarMap l E X)) := by
  classical
  let A := IntegralConstantCompletion.integers l E
  let I := IntegralConstantCompletion.ideal l E
  let J := Scheme.coefficientProEtaleModelTopology.{u, u} X
  obtain ⟨β, hβ⟩ := integralModels_residueIdealComparison l E X
  let : IsNoetherianRing A := IntegralConstantCompletion.integers_noetherian l E
  let : I.IsPrime := integers_prime l E
  let L := (ConstantCompletion.kernelIdeal (smallMap X (residueMap l E X))).extension
    (smallMap X (scalarMap l E X))
  apply extension_radical_iso ((Scheme.sfbModelRings X).mapIso (completedSectionIso l E X))
    _ L l (first_kernel_small l E X)
  intro U
  change L.sections U = _
  rw [hβ U]
  rw [first_kernel_radical J A I l (integers_radical l E)]
  exact comap_radical_nat
    (((sheafToPresheaf J CommRingCat).mapIso β).app (op U)).commRingCatIsoToRingEquiv l

end AlgebraicGeometry.ProEtale.IntegralModelsStacks
