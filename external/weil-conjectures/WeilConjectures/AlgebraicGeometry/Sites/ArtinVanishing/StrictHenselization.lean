/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.Unramified.LocalStructure
public import WeilConjectures.Mathlib.RingTheory.RegularLocalRing.Defs
public import WeilConjectures.AlgebraicGeometry.Sites.StrictHenselizationLocal
public import WeilConjectures.AlgebraicGeometry.Sites.ArtinVanishing.Algebra

/-!
# The strict henselization of a regular domain

Let `P` be a regular domain and `s : Spec Ω ⟶ Spec P` a geometric point. The strict
henselization `R = 𝒪^{sh}_{Spec P, s}` is the colimit of the rings of the pointed étale
neighbourhoods `Spec A ⟶ Spec P` of `s`. We show:

* `R` is a domain: the local rings of the étale `P`-algebras `A` at the image of `s` are regular,
  hence domains, and an element of `A` which vanishes in such a local ring already vanishes in
  `R`, being killed by an element invertible in `R`;
* `P ⟶ R` is injective, and `R` is algebraic over `P` (étale algebras over a domain are
  algebraic);
* if `s` lies over the generic point of `Spec P`, then `R` is a field.
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry.Scheme

variable {P : CommRingCat.{u}} {Ω : Type u} [Field Ω] [IsSepClosed Ω]
  (s : Spec (.of Ω) ⟶ Spec P)

/-- The canonical ring homomorphism `P ⟶ 𝒪^{sh}_{Spec P, s}` from a ring to the strict
henselization at a geometric point of its spectrum. -/
noncomputable def toStrictHenselization : P ⟶ strictHenselization s :=
  Spec.preimage (strictLocalizationToBase s)

/-- Evaluating the image of `P` in the strict henselization at the geometric point gives the
ring homomorphism `P ⟶ Ω` of `s`. -/
lemma toStrictHenselization_comp_strictHenselizationEval :
    toStrictHenselization s ≫ strictHenselizationEval s = Spec.preimage s := by
  rw [← Spec.preimage_map (toStrictHenselization s ≫ strictHenselizationEval s), Spec.map_comp,
    toStrictHenselization, Spec.map_preimage,
    spec_map_strictHenselizationEval_comp_strictLocalizationToBase]

namespace SpecPointedEtaleNeighborhood

variable {s}

/-- The pointed étale neighbourhood `(Spec P, s)` of `s`. -/
noncomputable def base : SpecPointedEtaleNeighborhood s :=
  ⟨P, 𝟙 _, inferInstance, Spec.preimage s, by simp⟩

set_option backward.isDefEq.respectTransparency false in
/-- The map from the base neighbourhood is the canonical map `P ⟶ 𝒪^{sh}_{Spec P, s}`. -/
lemma base_ι : (base (s := s)).ι = toStrictHenselization s := by
  have h : Spec.map (Scheme.ΓSpecIso P).inv = inv (Spec P).toSpecΓ :=
    IsIso.eq_inv_of_hom_inv_id (toSpecΓ_SpecMap_ΓSpecIso_inv P)
  apply Spec.map_injective
  rw [toStrictHenselization, Spec.map_preimage,
    ← strictLocalizationCone_π_app_hom s base.toAffine, strictLocalizationCone_π_app,
    ι, Spec.map_comp]
  change _ ≫ Spec.map (Scheme.ΓSpecIso P).inv = (_ ≫ inv (Spec P).toSpecΓ) ≫ 𝟙 _
  rw [h, Category.comp_id]

/-- The structure map `P ⟶ R` of a pointed étale neighbourhood `Spec R` of `s`. -/
noncomputable def toR (N : SpecPointedEtaleNeighborhood s) : P ⟶ N.R :=
  Spec.preimage N.hom

omit [IsSepClosed Ω] in
/-- The structure map of a neighbourhood is étale. -/
lemma etale_toR (N : SpecPointedEtaleNeighborhood s) : N.toR.hom.Etale :=
  (HasRingHomProperty.Spec_iff (P := @Etale)).mp (by rw [toR, Spec.map_preimage]; infer_instance)

omit [IsSepClosed Ω] in
/-- The point of a neighbourhood restricts to the point `P ⟶ Ω` of `s`. -/
lemma toR_pt (N : SpecPointedEtaleNeighborhood s) : N.toR ≫ N.pt = Spec.preimage s := by
  rw [← Spec.preimage_map (N.toR ≫ N.pt), Spec.map_comp, toR, Spec.map_preimage, N.w]

/-- The structure map of a neighbourhood is compatible with the maps to the strict
henselization. -/
lemma toR_ι (N : SpecPointedEtaleNeighborhood s) : N.toR ≫ N.ι = toStrictHenselization s := by
  rw [← base_ι]
  exact comp_ι (N := base) (N' := N) N.toR
    (show Spec.map (Spec.preimage N.hom) ≫ 𝟙 _ = N.hom by
      rw [Category.comp_id, Spec.map_preimage])
    N.toR_pt

/-- The kernel of the point of a neighbourhood is a prime ideal. -/
instance (N : SpecPointedEtaleNeighborhood s) : (RingHom.ker N.pt.hom).IsPrime :=
  RingHom.ker_isPrime _

/-- An element of `R` killed by an element with nonzero value at the geometric point vanishes
in the strict henselization. -/
lemma ι_eq_zero_of_mul_eq_zero (N : SpecPointedEtaleNeighborhood s) {g c : N.R}
    (hg : N.pt g ≠ 0) (h : g * c = 0) : N.ι c = 0 := by
  have hu : IsUnit (N.ι g) := by
    rw [isUnit_iff_strictHenselizationEval_ne_zero, strictHenselizationEval_ι]
    exact hg
  rw [← hu.mul_right_eq_zero, ← map_mul, h, map_zero]

/-- An element of `R` vanishing in the localization at the kernel of the point vanishes in the
strict henselization. -/
lemma ι_eq_zero_of_algebraMap_eq_zero (N : SpecPointedEtaleNeighborhood s) {c : N.R}
    (h : algebraMap N.R (Localization.AtPrime (RingHom.ker N.pt.hom)) c = 0) : N.ι c = 0 := by
  obtain ⟨⟨g, hg⟩, hgc⟩ := (IsLocalization.map_eq_zero_iff
    (RingHom.ker N.pt.hom).primeCompl _ c).mp h
  exact N.ι_eq_zero_of_mul_eq_zero (fun h' ↦ hg (RingHom.mem_ker.mpr h')) hgc

omit [IsSepClosed Ω] in
/-- The local ring of a neighbourhood at its point is a domain, being regular. -/
lemma isDomain_localization [IsRegularRing P] (N : SpecPointedEtaleNeighborhood s) :
    IsDomain (Localization.AtPrime (RingHom.ker N.pt.hom)) := by
  let := N.toR.hom.toAlgebra
  have : Algebra.Etale P N.R := N.etale_toR
  have := IsRegularLocalRing.localization_of_etale (R := P) (RingHom.ker N.pt.hom)
  infer_instance

set_option backward.isDefEq.respectTransparency.types false in
/-- The pointed étale neighbourhood `Spec Γ(V, 𝒪_V)` given by an affine pointed étale
neighbourhood `(V, v)`. -/
noncomputable def ofAffine (y : AffinePointedEtaleNeighborhood s) :
    SpecPointedEtaleNeighborhood s where
  R := Γ(y.obj.1.left, ⊤)
  hom := inv y.obj.1.left.toSpecΓ ≫ y.obj.1.hom
  etale := by
    have : Etale y.obj.1.hom := y.obj.1.prop
    infer_instance
  pt := Scheme.Γ.map y.obj.2.left.op ≫ (Scheme.ΓSpecIso (.of Ω)).hom
  w := by
    have hy : Spec.map (Scheme.Γ.map y.obj.2.left.op ≫ (Scheme.ΓSpecIso (.of Ω)).hom) =
        y.obj.2.left ≫ y.obj.1.left.toSpecΓ := by
      rw [Spec.map_comp, SpecMap_ΓSpecIso_hom, Scheme.Γ_map_op]
      exact (Scheme.toSpecΓ_naturality _).symm
    rw [hy, Category.assoc, IsIso.hom_inv_id_assoc]
    exact CategoryTheory.Over.w y.obj.2

/-- For `φ : X ⟶ Spec R`, the composite `X ⟶ Spec Γ(X) ⟶ Spec Γ(Spec R) ≅ Spec R`
is `φ`. -/
lemma toSpecΓ_comp_map_ΓSpecIso_inv {X : Scheme.{u}} {R : CommRingCat.{u}} (φ : X ⟶ Spec R) :
    X.toSpecΓ ≫ Spec.map (Scheme.Γ.map φ.op) ≫ Spec.map (Scheme.ΓSpecIso R).inv = φ := by
  rw [Scheme.Γ_map_op, ← Category.assoc, ← Scheme.toSpecΓ_naturality, Category.assoc,
    toSpecΓ_SpecMap_ΓSpecIso_inv, Category.comp_id]

set_option backward.isDefEq.respectTransparency false in
/-- If an element of `R` vanishes in the strict henselization, then it already vanishes in a
refinement of the neighbourhood `Spec R`. -/
lemma exists_eq_zero_of_ι_eq_zero (N : SpecPointedEtaleNeighborhood s) {c : N.R}
    (h : N.ι c = 0) : ∃ (N' : SpecPointedEtaleNeighborhood s) (u : N.R ⟶ N'.R),
      Spec.map u ≫ N.hom = N'.hom ∧ u ≫ N'.pt = N.pt ∧ u c = 0 := by
  have h' : colimit.ι (strictHenselizationDiagram s) (op N.toAffine)
      ((Scheme.ΓSpecIso N.R).inv c) =
        colimit.ι (strictHenselizationDiagram s) (op N.toAffine) 0 := by
    rw [map_zero]; exact h
  obtain ⟨k, f, g, hf⟩ := Concrete.colimit_exists_of_rep_eq.{u} _ _ _ h'
  rw [map_zero] at hf
  let y := k.unop
  let φ : y.obj.1.left ⟶ Spec N.R := f.unop.hom.1.left
  have hφ : φ ≫ N.hom = y.obj.1.hom := f.unop.hom.1.w.trans (Category.comp_id _)
  have hφ' : y.obj.2.left ≫ φ = Spec.map N.pt := congrArg CommaMorphism.left f.unop.hom.2
  refine ⟨ofAffine y, (Scheme.ΓSpecIso N.R).inv ≫ Scheme.Γ.map φ.op, ?_, ?_, hf⟩
  · change _ = inv y.obj.1.left.toSpecΓ ≫ y.obj.1.hom
    rw [IsIso.eq_inv_comp, ← hφ, ← Category.assoc, Spec.map_comp,
      toSpecΓ_comp_map_ΓSpecIso_inv]
  · change _ ≫ Scheme.Γ.map y.obj.2.left.op ≫ (Scheme.ΓSpecIso (.of Ω)).hom = _
    rw [Category.assoc, ← Category.assoc (Scheme.Γ.map φ.op), ← Scheme.Γ.map_comp,
      ← op_comp, hφ', Scheme.Γ_map_op, Scheme.ΓSpecIso_naturality, Iso.inv_hom_id_assoc]

end SpecPointedEtaleNeighborhood

open SpecPointedEtaleNeighborhood

/-- The strict henselization of a regular domain is a domain. -/
theorem isDomain_strictHenselization [IsDomain P] [IsRegularRing P] :
    IsDomain (strictHenselization s) := by
  refine @NoZeroDivisors.to_isDomain _ _ _ ⟨fun {a b} hab ↦ ?_⟩
  obtain ⟨N, hN⟩ := exists_specPointedEtaleNeighborhood_forall_mem_range 2 ![a, b]
  obtain ⟨a', rfl⟩ := hN 0
  obtain ⟨b', rfl⟩ := hN 1
  rw [← map_mul] at hab
  obtain ⟨N', u, hu, hu', h0⟩ := N.exists_eq_zero_of_ι_eq_zero hab
  have hι := comp_ι u hu hu'
  have := N'.isDomain_localization
  have h1 : algebraMap N'.R (Localization.AtPrime (RingHom.ker N'.pt.hom)) (u a') *
      algebraMap N'.R (Localization.AtPrime (RingHom.ker N'.pt.hom)) (u b') = 0 := by
    rw [← map_mul, ← map_mul, h0, map_zero]
  rw [← hι, CommRingCat.comp_apply, CommRingCat.comp_apply]
  rcases mul_eq_zero.mp h1 with h | h
  · exact Or.inl (N'.ι_eq_zero_of_algebraMap_eq_zero h)
  · exact Or.inr (N'.ι_eq_zero_of_algebraMap_eq_zero h)

/-- A regular domain injects into its strict henselizations. -/
theorem injective_toStrictHenselization [IsDomain P] [IsRegularRing P] :
    Function.Injective (toStrictHenselization s) := by
  rw [injective_iff_map_eq_zero]
  intro c hc
  rw [← base_ι] at hc
  obtain ⟨N', u, hu, -, h0⟩ := base.exists_eq_zero_of_ι_eq_zero hc
  have hu : u = N'.toR := by
    rw [toR, ← hu]
    change u = Spec.preimage (Spec.map u ≫ 𝟙 _)
    rw [Category.comp_id, Spec.preimage_map]
  subst hu
  let := N'.toR.hom.toAlgebra
  have : Algebra.Etale P N'.R := N'.etale_toR
  have : Nontrivial N'.R := N'.pt.hom.domain_nontrivial
  by_contra hc0
  have hreg := Module.Flat.isSMulRegular_of_nonZeroDivisors (M := N'.R)
    (mem_nonZeroDivisors_of_ne_zero hc0)
  refine one_ne_zero (α := N'.R) (hreg ?_)
  change c • (1 : N'.R) = c • 0
  rw [smul_zero, Algebra.smul_def, mul_one]
  exact h0

/-- The strict henselization of a domain is algebraic over it. -/
theorem isAlgebraic_strictHenselization [IsDomain P] :
    let := (toStrictHenselization s).hom.toAlgebra
    Algebra.IsAlgebraic P (strictHenselization s) := by
  let := (toStrictHenselization s).hom.toAlgebra
  refine ⟨fun a ↦ ?_⟩
  obtain ⟨N, hN⟩ := exists_specPointedEtaleNeighborhood_forall_mem_range 1 ![a]
  obtain ⟨c, rfl⟩ := hN 0
  let := N.toR.hom.toAlgebra
  have : Algebra.Etale P N.R := N.etale_toR
  let e : N.R →ₐ[P] strictHenselization s :=
    { N.ι.hom with
      commutes' r := by
        change N.ι (N.toR r) = toStrictHenselization s r
        rw [← toR_ι N, CommRingCat.comp_apply] }
  have := Algebra.IsAlgebraic.of_etale P N.R
  exact (Algebra.IsAlgebraic.isAlgebraic c).algHom e

/-- If the geometric point `s` lies over the generic point of `Spec P`, i.e. `P ⟶ Ω` is
injective, then the strict henselization is a field. -/
theorem isField_strictHenselization [IsDomain P] [IsRegularRing P]
    (hs : Function.Injective (Spec.preimage s)) :
    IsField (strictHenselization s) := by
  rw [IsLocalRing.isField_iff_maximalIdeal_eq, eq_bot_iff]
  intro a ha
  rw [mem_maximalIdeal_strictHenselization_iff] at ha
  obtain ⟨N, hN⟩ := exists_specPointedEtaleNeighborhood_forall_mem_range 1 ![a]
  obtain ⟨c, rfl⟩ := hN 0
  rw [strictHenselizationEval_ι] at ha
  rw [Ideal.mem_bot]
  let := N.toR.hom.toAlgebra
  have : Algebra.Etale P N.R := N.etale_toR
  have := N.isDomain_localization
  set p := RingHom.ker N.pt.hom
  set Q := (⊥ : Ideal (Localization.AtPrime p)).comap (algebraMap N.R _)
  have hQ : Q.IsPrime := Ideal.comap_isPrime _ _
  have hQp : Q ≤ p :=
    le_trans (Ideal.comap_mono bot_le) Localization.AtPrime.under_maximalIdeal.le
  have hp : p.under P = ⊥ := by
    rw [eq_bot_iff]
    intro r hr
    rw [Ideal.mem_bot]
    apply hs
    rw [Ideal.under, Ideal.mem_comap, RingHom.mem_ker] at hr
    rw [map_zero, ← toR_pt N, CommRingCat.comp_apply]
    exact hr
  have hQp' : Q = p := Algebra.QuasiFinite.eq_of_le_of_under_eq (R := P) Q p hQp
    (le_antisymm (Ideal.comap_mono hQp) (hp ▸ bot_le))
  have hc : c ∈ Q := hQp' ▸ RingHom.mem_ker.mpr ha
  exact N.ι_eq_zero_of_algebraMap_eq_zero hc

end AlgebraicGeometry.Scheme
