import Langlands.Geometry.Analytic.FiniteBanachEtaleAffinoidQuotient
import Langlands.AlgebraicGeometry.FiniteEtale.EqualizerAlgebraProof
import Langlands.AlgebraicGeometry.FiniteLocallyFreeInvariantRingQuotientProof
import Langlands.Geometry.Analytic.AffineAnalytificationFiniteCharts
import Langlands.Geometry.Analytic.EtaleOpenMap.FiniteBanachLyingOver
import Langlands.Geometry.Analytic.GeneralizedAffinoid.FiniteAffinoidAlgebraDescent.FiniteBanachPresentation
import Langlands.Geometry.Analytic.GeneralizedAffinoid.Noetherian

/-! # Affinoid realizations of finite étale relation quotients -/

noncomputable section

universe u

namespace Langlands.Analytic.PresentedAffinoidAlgebra

open CategoryTheory

variable {K : Type u} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {A B C : PresentedAffinoidAlgebra K}

/-- A realized affinoid quotient of a finite étale relation on `B` over `A`.
The relation square is the actual pushout of the coefficient rings. -/
structure FiniteEtaleAffinoidQuotient
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

namespace FiniteEtaleAffinoidQuotient

open AffineAnalytification.FiniteCharts in
theorem baseMap_isFiniteBanach
    {f : BoundedAlgHom K A B} {s t : BoundedAlgHom K B C}
    (Q : FiniteEtaleAffinoidQuotient f s t) : Q.baseMap.IsFiniteBanach :=
  isFiniteBanach_of_finite _ Q.baseMap_finiteEtale.1

open AffineAnalytification.FiniteCharts in
theorem coverMap_isFiniteBanach
    {f : BoundedAlgHom K A B} {s t : BoundedAlgHom K B C}
    (Q : FiniteEtaleAffinoidQuotient f s t) : Q.coverMap.IsFiniteBanach :=
  isFiniteBanach_of_finite _ Q.coverMap_finiteEtale.1

theorem coverMap_spectrum_surjective
    {f : BoundedAlgHom K A B} {s t : BoundedAlgHom K B C}
    (Q : FiniteEtaleAffinoidQuotient f s t) :
    Function.Surjective (BanachSpectrum.comap Q.coverMap.toBoundedRingHom) := by
  intro x
  apply BanachSpectrum.exists_comap_eq_of_isFiniteBanach _ Q.coverMap_isFiniteBanach
  rw [(RingHom.injective_iff_ker_eq_bot Q.coverMap.toAlgHom.toRingHom).mp
    Q.coverMap_injective]
  exact bot_le

end FiniteEtaleAffinoidQuotient

open AffineAnalytification.FiniteCharts in
/-- The finite locally free algebraic quotient, with the inherited
equalizer norm and an actual affinoid presentation. -/
def finiteEtaleAffinoidQuotient
    (f : BoundedAlgHom K A B) (s t : BoundedAlgHom K B C)
    (hf : f.AlgebraicallyFiniteEtale)
    (hs : s.AlgebraicallyFiniteEtale) (ht : t.AlgebraicallyFiniteEtale)
    (hcomp : s.comp f = t.comp f)
    (hgen : s.toAlgHom.toRingHom.range ⊔ t.toAlgHom.toRingHom.range = ⊤)
    (hrel : ∀ (T : Type u) [CommRing T],
      _root_.Equivalence fun x y : B →+* T => ∃ φ : C →+* T,
        φ.comp s.toAlgHom.toRingHom = x ∧ φ.comp t.toAlgHom.toRingHom = y) :
    FiniteEtaleAffinoidQuotient f s t := by
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
  have hD1 : ‖(1 : D)‖ ≤ 1 := PresentedAffinoidAlgebra.norm_one_le K B
  let presentation := FiniteBanachPresentation.exists_presentation g hD1
    (isFiniteBanach_of_finite g hEtale.1)
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
  have hcoverInj : Function.Injective cover := hi.comp e.toAlgEquiv.injective
  have projective (r : BoundedAlgHom K B C) (hr : r.AlgebraicallyFiniteEtale) :
      letI := r.toAlgHom.toRingHom.toAlgebra; Module.Projective B C := by
    let : Algebra B C := r.toAlgHom.toRingHom.toAlgebra
    let : Module.Finite B C := hr.1
    let : Algebra.Etale B C := hr.2
    let : Module.FinitePresentation B C := Module.finitePresentation_of_finite B C
    exact Module.Flat.projective_of_finitePresentation
  letI : Algebra P B := cover.toAlgHom.toRingHom.toAlgebra
  have hInv (b : B) : s b = t b ↔ b ∈ Set.range (algebraMap P B) := by
    constructor
    · intro hb
      let d : D := ⟨b, hb⟩
      exact ⟨e.symm d, congrArg Subtype.val (e.toAlgEquiv.apply_symm_apply d)⟩
    · rintro ⟨p, rfl⟩
      exact (e p).property
  obtain ⟨hCoverFin, -, hCoverFF, hPush⟩ :=
    Langlands.AlgebraicGeometry.FiniteLocallyFreeQuotient.invariantRingQuotient
      s.toAlgHom.toRingHom t.toAlgHom.toRingHom hs.1 (projective s hs) ht.1 (projective t ht)
      hgen hrel hcoverInj hInv
  have hCoverEtale : cover.toAlgHom.toRingHom.Etale := by
    let : Algebra A P := base.toAlgHom.toRingHom.toAlgebra
    let : IsScalarTower A P B := IsScalarTower.of_algebraMap_eq (fun a =>
      (congrArg (fun r : BoundedAlgHom K A B => r a) hfac).symm)
    let : Algebra.Etale A B := hf.2
    let : Module.Finite P B := hCoverFin
    let : Module.FaithfullyFlat P B := hCoverFF
    let : Algebra.FinitePresentation P B := Algebra.FinitePresentation.of_finiteType.mp
      (show cover.toAlgHom.toRingHom.Finite from hCoverFin).finiteType
    let : Algebra.FormallyUnramified P B :=
      Algebra.FormallyUnramified.of_restrictScalars A P B
    exact Algebra.Etale.of_formallyUnramified_of_flat
  exact ⟨P, base, cover, hfac, hbase, ⟨hCoverFin, hCoverEtale⟩, hcoverInj, hPush⟩

end Langlands.Analytic.PresentedAffinoidAlgebra
