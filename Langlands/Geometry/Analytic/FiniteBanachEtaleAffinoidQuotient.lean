import Langlands.AlgebraicGeometry.FiniteEtale.EqualizerAlgebraProof
import Langlands.AlgebraicGeometry.FiniteLocallyFreeInvariantRingQuotientProof
import Langlands.Geometry.Analytic.AffineAnalytificationFiniteCharts
import Langlands.Geometry.Analytic.EtaleOpenMap.FiniteBanachLyingOver
import Langlands.Geometry.Analytic.FiniteBanachCancellation
import Langlands.Geometry.Analytic.FiniteEtaleSourcePieces
import Langlands.Geometry.Analytic.FiniteMorphismSmallNeighborhoods
import Langlands.Geometry.Analytic.GeneralizedAffinoid.FiniteAffinoidAlgebraDescent.FiniteBanachPresentation
import Langlands.Geometry.Analytic.GeneralizedAffinoid.Noetherian

/-! # Affinoid realizations of finite étale relation quotients -/

noncomputable section

universe u

namespace Langlands.Analytic.PresentedAffinoidAlgebra

open CategoryTheory

section

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {A B C : PresentedAffinoidAlgebra K}

/-- A realized affinoid quotient of a finite étale relation on `B` over `A`.
The relation square is the actual pushout of the coefficient rings. -/
structure FiniteBanachEtaleAffinoidQuotient
    (f : BoundedAlgHom K A B) (s t : BoundedAlgHom K B C) where
  algebra : PresentedAffinoidAlgebra K
  baseMap : BoundedAlgHom K A algebra
  coverMap : BoundedAlgHom K algebra B
  coverMap_comp : coverMap.comp baseMap = f
  baseMap_finiteEtale : baseMap.AlgebraicallyFiniteEtale
  coverMap_finiteEtale : coverMap.AlgebraicallyFiniteEtale
  coverMap_injective : Function.Injective coverMap
  relation_isPushout : IsPushout
    (CommRingCat.ofHom coverMap.toAlgHom.toRingHom)
    (CommRingCat.ofHom coverMap.toAlgHom.toRingHom)
    (CommRingCat.ofHom s.toAlgHom.toRingHom) (CommRingCat.ofHom t.toAlgHom.toRingHom)

omit [CompleteSpace K] in
theorem FiniteBanachEtaleAffinoidQuotient.coverMap_spectrum_surjective_of_isFiniteBanach
    {f : BoundedAlgHom K A B} {s t : BoundedAlgHom K B C}
    (Q : FiniteBanachEtaleAffinoidQuotient f s t) (hBanach : Q.coverMap.IsFiniteBanach) :
    Function.Surjective (BanachSpectrum.comap Q.coverMap.toBoundedRingHom) := by
  intro x
  apply BanachSpectrum.exists_comap_eq_of_isFiniteBanach _ hBanach
  rw [(RingHom.injective_iff_ker_eq_bot Q.coverMap.toAlgHom.toRingHom).mp
    Q.coverMap_injective]
  exact bot_le

/-- The finite locally free algebraic quotient, with the inherited
equalizer norm and an actual affinoid presentation. Finite Banach
structure on `f` supplies finite Banach structure on both factors. -/
def finiteEtaleAffinoidQuotientOfFiniteBanach
    (f : BoundedAlgHom K A B) (s t : BoundedAlgHom K B C)
    (hfBanach : f.IsFiniteBanach) (hf : f.AlgebraicallyFiniteEtale)
    (hs : s.AlgebraicallyFiniteEtale) (ht : t.AlgebraicallyFiniteEtale)
    (hcomp : s.comp f = t.comp f)
    (hgen : s.toAlgHom.toRingHom.range ⊔ t.toAlgHom.toRingHom.range = ⊤)
    (hrel : ∀ (T : Type u) [CommRing T],
      _root_.Equivalence fun x y : B →+* T => ∃ φ : C →+* T,
        φ.comp s.toAlgHom.toRingHom = x ∧ φ.comp t.toAlgHom.toRingHom = y) :
    {Q : FiniteBanachEtaleAffinoidQuotient f s t //
      Q.baseMap.IsFiniteBanach ∧ Q.coverMap.IsFiniteBanach} := by
  letI : Algebra A B := f.toAlgHom.toRingHom.toAlgebra
  letI : Algebra A C := (s.comp f).toAlgHom.toRingHom.toAlgebra
  letI : IsScalarTower K A B := IsScalarTower.of_algebraMap_eq' f.toAlgHom.comp_algebraMap.symm
  let sA : B →ₐ[A] C := { s.toAlgHom.toRingHom with commutes' := fun _ => rfl }
  let tA : B →ₐ[A] C := { t.toAlgHom.toRingHom with
    commutes' := fun a => (congrArg (fun r : BoundedAlgHom K A C => r a) hcomp).symm }
  let S := sA.equalizer tA
  let D := S.restrictScalars K
  have hClosed : IsClosed (D : Set B) := isClosed_eq s.continuous t.continuous
  letI : CompleteSpace D := hClosed.completeSpace_coe
  letI : IsUltrametricDist D := inferInstanceAs (IsUltrametricDist {b : B // b ∈ D})
  let g : BoundedAlgHom K A D := {
    toAlgHom := f.toAlgHom.codRestrict D (fun a =>
      congrArg (fun r : BoundedAlgHom K A C => r a) hcomp)
    bounded := f.bounded }
  let i : BoundedAlgHom K D B := ⟨D.val, ⟨1, zero_lt_one, fun _ => by rw [one_mul]; rfl⟩⟩
  have hi : Function.Injective i := Subtype.val_injective
  have hgcomp : i.comp g = f := by ext a; rfl
  have hEtale : g.AlgebraicallyFiniteEtale := by
    let : Module.Finite A B := hf.1
    let : Algebra.Etale A B := hf.2
    let : Module.Finite A C := (hs.comp hf).1
    let : Algebra.Etale A C := (hs.comp hf).2
    obtain ⟨hSfin, hSetale⟩ :=
      Langlands.AlgebraicGeometry.FiniteEtale.equalizerAlgebraFiniteEtale A B C sA tA
    change (algebraMap A S).Finite ∧ (algebraMap A S).Etale
    exact ⟨RingHom.finite_algebraMap.2 hSfin, RingHom.etale_algebraMap.2 hSetale⟩
  have projective (r : BoundedAlgHom K B C) (hr : r.AlgebraicallyFiniteEtale) :
      letI := r.toAlgHom.toRingHom.toAlgebra; Module.Projective B C := by
    let : Algebra B C := r.toAlgHom.toRingHom.toAlgebra
    let : Module.Finite B C := hr.1
    let : Algebra.Etale B C := hr.2
    let : Module.FinitePresentation B C := Module.finitePresentation_of_finite B C
    exact Module.Flat.projective_of_finitePresentation
  letI : Algebra D B := i.toAlgHom.toRingHom.toAlgebra
  have hInv (b : B) : s b = t b ↔ b ∈ Set.range (algebraMap D B) :=
    ⟨fun hb => ⟨⟨b, hb⟩, rfl⟩, fun ⟨d, hd⟩ => hd ▸ d.property⟩
  obtain ⟨-, hProj, hFF, hPush⟩ :=
    Langlands.AlgebraicGeometry.FiniteLocallyFreeQuotient.invariantRingQuotient
      s.toAlgHom.toRingHom t.toAlgHom.toRingHom hs.1 (projective s hs) ht.1 (projective t ht)
      hgen hrel hi hInv
  have hgBanach : g.IsFiniteBanach := by
    have hComp : (i.comp g).IsFiniteBanach := hgcomp ▸ hfBanach
    exact hComp.of_faithfullyFlat_comp_of_projective hProj hFF
  have hD1 : ‖(1 : D)‖ ≤ 1 := PresentedAffinoidAlgebra.norm_one_le K B
  let presentation := FiniteBanachPresentation.exists_presentation g hD1 hgBanach
  let P := presentation.choose
  let e : BoundedAlgEquiv K P D := Classical.choice presentation.choose_spec
  let cover := i.comp e.toBoundedAlgHom
  let base := e.symm.toBoundedAlgHom.comp g
  have hfac : cover.comp base = f := by
    rw [← hgcomp]
    ext a
    change (e (e.symm (g a)) : D).val = (g a).val
    exact congrArg Subtype.val (e.toAlgEquiv.apply_symm_apply (g a))
  have hbase : base.AlgebraicallyFiniteEtale := by
    exact (BoundedAlgHom.AlgebraicallyFiniteEtale.of_bijective _
      e.toAlgEquiv.symm.bijective).comp hEtale
  have hBaseBanach : base.IsFiniteBanach := by
    obtain ⟨M, hM, hb⟩ := e.bounded
    have hInverse : e.symm.toBoundedAlgHom.IsFiniteBanach :=
      BoundedAlgHom.isFiniteBanach_of_lift _ hM fun z => ⟨e z, e.symm_apply_apply z, hb z⟩
    exact hInverse.comp hgBanach
  have hCoverBanach : cover.IsFiniteBanach := by
    have hComp : (cover.comp base).IsFiniteBanach := hfac ▸ hfBanach
    exact hComp.of_comp
  have hCoverEtale : cover.toAlgHom.toRingHom.Etale := by
    let : Algebra P B := cover.toAlgHom.toRingHom.toAlgebra
    let : Algebra A P := base.toAlgHom.toRingHom.toAlgebra
    let : IsScalarTower A P B := IsScalarTower.of_algebraMap_eq (fun a =>
      (congrArg (fun r : BoundedAlgHom K A B => r a) hfac).symm)
    let : Algebra.Etale A B := hf.2
    let : Module.Finite P B := hCoverBanach.finite
    let : Module.FaithfullyFlat P B :=
      RingHom.FaithfullyFlat.stableUnderComposition _ _
        (RingHom.FaithfullyFlat.of_bijective e.toAlgEquiv.bijective) hFF
    let : Algebra.FinitePresentation P B := Algebra.FinitePresentation.of_finiteType.mp
      hCoverBanach.finite.finiteType
    let : Algebra.FormallyUnramified P B :=
      Algebra.FormallyUnramified.of_restrictScalars A P B
    exact Algebra.Etale.of_formallyUnramified_of_flat
  refine ⟨⟨P, base, cover, hfac, hbase, ⟨hCoverBanach.finite, hCoverEtale⟩,
    hi.comp e.toAlgEquiv.injective, ?_⟩, hBaseBanach, hCoverBanach⟩
  exact hPush.of_iso' e.toAlgEquiv.toRingEquiv.toCommRingCatIso
    (Iso.refl _) (Iso.refl _) (Iso.refl _)
    (by rw [Iso.refl_hom, Category.comp_id]; rfl)
    (by rw [Iso.refl_hom, Category.comp_id]; rfl)
    (by simp) (by simp)

end

variable {K : Type u} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {A B C : PresentedAffinoidAlgebra K}

namespace FiniteBanachEtaleAffinoidQuotient

open AffineAnalytification.FiniteCharts in
theorem baseMap_isFiniteBanach
    {f : BoundedAlgHom K A B} {s t : BoundedAlgHom K B C}
    (Q : FiniteBanachEtaleAffinoidQuotient f s t) : Q.baseMap.IsFiniteBanach :=
  isFiniteBanach_of_finite _ Q.baseMap_finiteEtale.1

open AffineAnalytification.FiniteCharts in
theorem coverMap_isFiniteBanach
    {f : BoundedAlgHom K A B} {s t : BoundedAlgHom K B C}
    (Q : FiniteBanachEtaleAffinoidQuotient f s t) : Q.coverMap.IsFiniteBanach :=
  isFiniteBanach_of_finite _ Q.coverMap_finiteEtale.1

theorem coverMap_spectrum_surjective
    {f : BoundedAlgHom K A B} {s t : BoundedAlgHom K B C}
    (Q : FiniteBanachEtaleAffinoidQuotient f s t) :
    Function.Surjective (BanachSpectrum.comap Q.coverMap.toBoundedRingHom) :=
  Q.coverMap_spectrum_surjective_of_isFiniteBanach Q.coverMap_isFiniteBanach

end FiniteBanachEtaleAffinoidQuotient

open AffineAnalytification.FiniteCharts in
/-- Over a nontrivially normed field, algebraic finiteness alone gives
the finite Banach structure of the composite. -/
def finiteBanachEtaleAffinoidQuotientOfFiniteness
    (f : BoundedAlgHom K A B) (s t : BoundedAlgHom K B C)
    (hf : f.AlgebraicallyFiniteEtale)
    (hs : s.AlgebraicallyFiniteEtale) (ht : t.AlgebraicallyFiniteEtale)
    (hcomp : s.comp f = t.comp f)
    (hgen : s.toAlgHom.toRingHom.range ⊔ t.toAlgHom.toRingHom.range = ⊤)
    (hrel : ∀ (T : Type u) [CommRing T],
      _root_.Equivalence fun x y : B →+* T => ∃ φ : C →+* T,
        φ.comp s.toAlgHom.toRingHom = x ∧ φ.comp t.toAlgHom.toRingHom = y) :
    FiniteBanachEtaleAffinoidQuotient f s t :=
  (finiteEtaleAffinoidQuotientOfFiniteBanach f s t (isFiniteBanach_of_finite f hf.1)
    hf hs ht hcomp hgen hrel).val

end Langlands.Analytic.PresentedAffinoidAlgebra
