import Langlands.AlgebraicGeometry.Modules.IdealAdicFibreSerre
import Langlands.AlgebraicGeometry.Modules.AffinePushforwardEulerCharacteristicProof
import Langlands.AlgebraicGeometry.Modules.FieldGlobalFunctionsAlgebra

/-! # Affineness across a nilpotent base reduction -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite TopologicalSpace
open Langlands.Scheme.Modules

namespace Langlands.AlgebraicGeometry.Modules

open DerivedSections IdealAdic

private theorem isIso_projection_of_eq_bot
    {R : CommRingCat.{u}} {X : Scheme.{u}} (f : X ⟶ Spec R)
    (J : Ideal R) (hJ : J = ⊥) (M : X.Modules) :
    IsIso (projection f J M) := by
  apply cokernel.π_of_zero
  rw [← Category.comp_id (inclusion f J M)]
  apply (inclusion_comp_eq_zero_iff f J (𝟙 M)).mpr
  intro U r hr t
  have hrZero : r = 0 := by simpa [hJ] using hr
  subst r
  simp

private theorem epi_map_of_factorization {C D : Type*} [Category C] [Category D]
    (F : C ⥤ D) {A B H : C} {a : A ⟶ B} {b : B ⟶ H} {d : A ⟶ H}
    (w : a ≫ b = d) (ha : Epi (F.map a)) (hb : Epi (F.map b)) :
    Epi (F.map d) := by
  subst d
  rw [F.map_comp]
  infer_instance

private theorem epi_sections_adicTransition
    {R : CommRingCat.{u}} {X : Scheme.{u}} (f : X ⟶ Spec R) (I : Ideal R)
    (M : X.Modules) (hLayers : ∀ n, IsZero ((relativeCohomology f 1).obj (adicLayer f I M n)))
    {j k : ℕ} (h : j ≤ k) :
    Epi ((relativeGlobalSections f).map (adicTransition f I M h)) :=
  (ModuleCat.epi_iff_surjective _).2 (surjective_sections_adicTransition f I M hLayers h)

private theorem epi_sections_adicProjection_one
    {R : CommRingCat.{u}} {X : Scheme.{u}} (f : X ⟶ Spec R) (I : Ideal R) (M : X.Modules)
    {k : ℕ} (hk : 1 ≤ k) (hTop : IsIso (adicProjection f I M k))
    (hTransition : Epi ((relativeGlobalSections f).map (adicTransition f I M hk))) :
    Epi ((relativeGlobalSections f).map (adicProjection f I M 1)) := by
  let Γf := relativeGlobalSections f
  have hcomp : adicProjection f I M k ≫ adicTransition f I M hk = adicProjection f I M 1 :=
    projection_quotientMap f _ M
  have hEpi : Epi (Γf.map (adicProjection f I M k)) := inferInstance
  exact epi_map_of_factorization Γf hcomp hEpi hTransition

private theorem epi_sections_adicProjection_one_of_nilpotent
    {R : CommRingCat.{u}} {X : Scheme.{u}} (f : X ⟶ Spec R) (I : Ideal R)
    (hI : IsNilpotent I) (M : X.Modules)
    (hLayers : ∀ n, IsZero ((relativeCohomology f 1).obj (adicLayer f I M n))) :
    Epi ((relativeGlobalSections f).map (adicProjection f I M 1)) := by
  obtain ⟨n, hn⟩ := hI
  have hpow : I ^ (n + 1) = ⊥ := by simp [pow_succ, hn]
  have hpos : 1 ≤ n + 1 := Nat.succ_le_succ (Nat.zero_le n)
  exact epi_sections_adicProjection_one f I M hpos (isIso_projection_of_eq_bot f _ hpow M)
    (epi_sections_adicTransition f I M hLayers hpos)

private theorem epi_sections_projection_of_adicLayers
    {R : CommRingCat.{u}} {X : Scheme.{u}} (f : X ⟶ Spec R) (I : Ideal R)
    (hI : IsNilpotent I) (M : X.Modules)
    (hLayers : ∀ n, IsZero ((relativeCohomology f 1).obj (adicLayer f I M n))) :
    Epi ((relativeGlobalSections f).map (projection f I M)) := by
  have hFirst : Epi ((relativeGlobalSections f).map (projection f (I ^ 1) M)) :=
    epi_sections_adicProjection_one_of_nilpotent f I hI M hLayers
  exact Eq.ndrec (motive := fun J => Epi ((relativeGlobalSections f).map (projection f J M)))
    hFirst (pow_one I)

private theorem isAffine_of_surjective_sections {X Z : Scheme.{u}} (i : Z ⟶ X)
    [IsAffine Z] [Surjective i] (hΓ : Function.Surjective i.appTop) : IsAffine X := by
  let s : Set Γ(X, ⊤) := {r | IsAffineOpen (X.basicOpen r)}
  apply isAffine_of_isAffineOpen_basicOpen s _ (fun _ hr => hr)
  have hcover : ⨆ r : i.appTop.hom '' s, Z.basicOpen r.1 = ⊤ := by
    apply top_unique
    intro z _
    obtain ⟨U, hU, hzU, -⟩ := exists_isAffineOpen_mem_and_subset
      (x := i z) (U := ⊤) trivial
    obtain ⟨a, ha, hza⟩ :=
      (isAffineOpen_top Z).exists_basicOpen_le (V := i ⁻¹ᵁ U) ⟨z, hzU⟩ trivial
    obtain ⟨r, hr⟩ := hΓ a
    have hpre : i ⁻¹ᵁ X.basicOpen r = Z.basicOpen a := by
      rw [i.preimage_basicOpen_top, hr]
    have hle : X.basicOpen r ≤ U := by
      intro x hx
      obtain ⟨y, rfl⟩ := i.surjective x
      apply ha
      rw [← hpre]
      exact hx
    have hrAffine : r ∈ s := by
      change IsAffineOpen (X.basicOpen r)
      have hh := hU.basicOpen (X.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op r)
      rw [X.basicOpen_res, inf_eq_right.mpr hle] at hh
      exact hh
    exact Opens.mem_iSup.mpr ⟨⟨a, ⟨r, hrAffine, hr⟩⟩, hza⟩
  have hspan : (Ideal.span s).map i.appTop.hom = ⊤ := by
    rw [Ideal.map_span]
    exact (isAffineOpen_top Z).iSup_basicOpen_eq_self_iff.mp hcover
  have hone : (1 : Γ(Z, ⊤)) ∈ (Ideal.span s).map i.appTop.hom := hspan ▸ trivial
  obtain ⟨r, hr, hrOne⟩ := (Ideal.mem_map_iff_of_surjective i.appTop.hom hΓ).mp hone
  have htop : X.basicOpen r = ⊤ := by
    apply top_unique
    intro x _
    obtain ⟨z, rfl⟩ := i.surjective x
    change z ∈ i ⁻¹ᵁ X.basicOpen r
    rw [i.preimage_basicOpen_top, hrOne, Z.basicOpen_of_isUnit isUnit_one]
    trivial
  have hu : IsUnit r := by
    apply X.toRingedSpace.isUnit_of_isUnit_germ ⊤ r
    intro x hx
    apply (X.mem_basicOpen r x hx).mp
    rw [htop]
    exact hx
  exact Ideal.eq_top_of_isUnit_mem _ hr hu

section

variable {R : CommRingCat.{u}} [IsNoetherianRing R] {X Z : Scheme.{u}}
  [IsLocallyNoetherian X] {f : X ⟶ Spec R} {I : Ideal R}
  {i : Z ⟶ X} {g : Z ⟶ Spec (CommRingCat.of (R ⧸ I))}

set_option maxHeartbeats 1000000 in
/-- When the actual reduction is affine, each successive ideal layer of
the structure module has vanishing first cohomology. -/
private theorem isZero_adicLayer [IsAffine Z]
    (hpb : IsPullback i g f (Spec.map (quotientRingHom I))) (n : ℕ) :
    IsZero ((relativeCohomology f 1).obj
      (adicLayer f I (SheafOfModules.unit X.ringCatSheaf) n)) := by
  let O := SheafOfModules.unit X.ringCatSheaf
  let L := adicLayer f I O n
  let : O.IsQuasicoherent := CechDegreeOne.isQuasicoherent_unit X
  have hO : HasFiniteAffineSections O := by
    intro U
    change Module.Finite Γ(X, U.1) Γ(X, U.1)
    infer_instance
  obtain ⟨hL, -, hann⟩ :=
    annihilatedCoherent_adicLayer f I (IsNoetherian.noetherian I) O hO n
  let P := (Scheme.Modules.pullback i).obj L
  have hP : P.IsQuasicoherent := inferInstance
  let e := closedFibreIsoOfAnnihilated hpb L hann
  have hi := isClosedImmersion_of_isPullback hpb
  have hz := (affineQuasicoherentCohomologyVanishing Z inferInstance P hP 0).2 R (i ≫ f)
  have hp : IsZero ((relativeCohomology f 1).obj ((Scheme.Modules.pushforward i).obj P)) :=
    hz.of_iso (affinePushforwardCohomologyIso i f P 1).symm
  exact hp.of_iso ((relativeCohomology f 1).mapIso e)

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 800000 in
private theorem epi_sections_structureMap_of_nilpotent_base [IsAffine Z]
    (hpb : IsPullback i g f (Spec.map (quotientRingHom I))) (hI : IsNilpotent I) :
    Epi ((relativeGlobalSections f).map (unitToPushforwardUnit i)) := by
  let O := SheafOfModules.unit X.ringCatSheaf
  let : O.IsQuasicoherent := CechDegreeOne.isQuasicoherent_unit X
  let fibreIso := closedFibreIso hpb O
  let pushUnitIso := (Scheme.Modules.pushforward i).mapIso (pullbackUnitIso i)
  have hFibre : projection f I O ≫ fibreIso.hom ≫ pushUnitIso.hom =
      unitToPushforwardUnit i := by
    change projection f I O ≫ (closedFibreIso hpb O).hom ≫
      (Scheme.Modules.pushforward i).map (pullbackUnitIso i).hom = _
    rw [← Category.assoc, projection_closedFibreIso_hom, FieldGlobalFunctions.pullbackUnitIso_unit]
  let Γf := relativeGlobalSections f
  let : Epi (Γf.map (projection f I O)) :=
    epi_sections_projection_of_adicLayers f I hI O (isZero_adicLayer hpb)
  have hm : Γf.map (projection f I O) ≫ Γf.map fibreIso.hom ≫ Γf.map pushUnitIso.hom =
      Γf.map (unitToPushforwardUnit i) := by
    rw [← Γf.map_comp, ← Γf.map_comp, hFibre]
  exact hm ▸ (inferInstance :
    Epi (Γf.map (projection f I O) ≫ Γf.map fibreIso.hom ≫ Γf.map pushUnitIso.hom))

/-- The actual map on global functions onto an affine nilpotent base
reduction is surjective. -/
theorem appTop_surjective_of_affine_nilpotent_base [IsAffine Z]
    (hpb : IsPullback i g f (Spec.map (quotientRingHom I))) (hI : IsNilpotent I) :
    Function.Surjective i.appTop := by
  have hepi := epi_sections_structureMap_of_nilpotent_base hpb hI
  intro z
  obtain ⟨r, hr⟩ := (ModuleCat.epi_iff_surjective _).mp hepi z
  exact ⟨r, hr⟩

/-- Affineness descends from the actual nilpotent base reduction over a
Noetherian ring. -/
theorem isAffine_of_affine_nilpotent_base [IsAffine Z]
    (hpb : IsPullback i g f (Spec.map (quotientRingHom I))) (hI : IsNilpotent I) :
    IsAffine X := by
  have hrad : I ≤ nilradical R := by
    intro a ha
    obtain ⟨n, hn⟩ := hI
    exact ⟨n, by simpa [hn] using Ideal.pow_mem_pow ha n⟩
  have hq : Surjective (Spec.map (quotientRingHom I)) :=
    ⟨(PrimeSpectrum.comap_quotientMk_bijective_of_le_nilradical hrad).2⟩
  let : Surjective i := MorphismProperty.of_isPullback (P := @Surjective) hpb.flip hq
  exact isAffine_of_surjective_sections i (appTop_surjective_of_affine_nilpotent_base hpb hI)

end

/-- Over a Noetherian affine base, a locally Noetherian scheme with an
affine nilpotent base reduction is affine. -/
def NilpotentBaseAffinenessStatement : Prop :=
  ∀ (R : CommRingCat.{u}) [IsNoetherianRing R]
    (X Z : Scheme.{u}) [IsLocallyNoetherian X] [IsAffine Z]
    (f : X ⟶ Spec R) (I : Ideal R) (i : Z ⟶ X) (g : Z ⟶ Spec (CommRingCat.of (R ⧸ I))),
    IsPullback i g f (Spec.map (quotientRingHom I)) → IsNilpotent I → IsAffine X

/-- Affineness is reflected by the actual nilpotent base pullback. -/
theorem nilpotentBaseAffineness : NilpotentBaseAffinenessStatement.{u} := by
  intro R _ X Z _ _ f I i g hpb hI
  exact isAffine_of_affine_nilpotent_base hpb hI

end Langlands.AlgebraicGeometry.Modules
