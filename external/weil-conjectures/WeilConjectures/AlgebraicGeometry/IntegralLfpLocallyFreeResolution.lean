/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ContinuousIntegralCoefficientData
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import WeilConjectures.ConstructibleSheaf.ProEtaleModule.Def
import all WeilConjectures.AlgebraicGeometry.IntegralConstructibleKernels
import WeilConjectures.AlgebraicGeometry.IntegralLfpEventualFreeImage
import all WeilConjectures.AlgebraicGeometry.IntegralLfpLocalTorsionCharts
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Images
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Kernels

/-! # A locally finite free resolution of a finitely presented integral local system -/

@[expose] public section

universe v u

open CategoryTheory Limits
open scoped CategoryTheory.Obj ZeroObject

variable {C : Type u} [Category.{v} C] [Abelian C]

-- Row elimination gives an actual epi-mono factorization of the block matrix.
private noncomputable def pivotImageIso {A B D E : C}
    (p : A ⟶ D) [Mono p] (r : B ⟶ A) (c : A ⟶ E) (d : B ⟶ E) :
    image (biprod.lift (biprod.desc p (r ≫ p)) (biprod.desc c d)) ≅
      A ⊞ image (d - r ≫ c) := by
  let s := d - r ≫ c
  let U : A ⊞ B ≅ A ⊞ B :=
    { hom := biprod.lift (biprod.desc (𝟙 A) r) biprod.snd
      inv := biprod.lift (biprod.desc (𝟙 A) (-r)) biprod.snd
      hom_inv_id := by ext <;> simp
      inv_hom_id := by ext <;> simp }
  let e := U.hom ≫ biprod.map (𝟙 A) (factorThruImage s)
  let m : A ⊞ image s ⟶ D ⊞ E :=
    biprod.lift (biprod.fst ≫ p) (biprod.desc c (image.ι s))
  have : IsIso U.hom := ⟨⟨U.inv, U.hom_inv_id, U.inv_hom_id⟩⟩
  have : Epi (factorThruImage s) := by infer_instance
  have : Epi (biprod.map (𝟙 A) (factorThruImage s)) := by infer_instance
  have : Epi e := by dsimp only [e]; infer_instance
  have : Mono m := by
    rw [Preadditive.mono_iff_cancel_zero]
    intro Z x hx
    have hx₁ : x ≫ biprod.fst = 0 := by
      apply (cancel_mono p).mp
      simpa [m] using hx =≫ biprod.fst
    have hx₂ : x ≫ biprod.snd = 0 := by
      apply (cancel_mono (image.ι s)).mp
      simpa [m, biprod.desc_eq, Preadditive.comp_add, reassoc_of% hx₁] using hx =≫ biprod.snd
    apply biprod.hom_ext <;> simp [hx₁, hx₂]
  have : StrongEpi e := strongEpi_of_epi e
  apply (image.isoStrongEpiMono e m ?_).symm
  ext <;> simp [e, U, m, s, biprod.desc_eq, Preadditive.comp_sub,
    Preadditive.add_comp, Preadditive.comp_add]

private noncomputable def resolutionImageIso {A B A' B' : C} (f : A ⟶ B) (g : A' ⟶ B')
    (i : A ≅ A') (j : B ≅ B') (w : f ≫ j.hom = i.hom ≫ g) : image f ≅ image g := by
  let e := i.inv ≫ factorThruImage f
  let m := image.ι f ≫ j.hom
  have : Epi e := by dsimp only [e]; infer_instance
  have : Mono m := by dsimp only [m]; infer_instance
  have : StrongEpi e := strongEpi_of_epi e
  exact image.isoStrongEpiMono e m (by simp [e, m, w])

namespace AlgebraicGeometry.ProEtale.CondensedRing
open MonoidalCategory MonObj
open Functor.LaxMonoidal Functor.OplaxMonoidal
attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits
attribute [local instance] preservesBinaryBiproducts_of_preservesBinaryCoproducts

private abbrev ResolutionLF {X : Scheme.{u}}
    (R : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) [MonObj R]
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) R) : Prop :=
  ∃ U : Scheme.Cover.{u} Scheme.proetalePrecoverage X, ∀ i,
    Mod.IsFree ((ProEtale.upperStar Ab.{u + 1} (U.f i)).obj R)
      (((ProEtale.upperStar Ab.{u + 1} (U.f i)).mapMod R).obj M)

private lemma resolutionLF_of_cover {X : Scheme.{u}}
    {R : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}} [MonObj R] [IsCommMonObj R]
    {M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) R}
    (U : Scheme.Cover.{u} Scheme.proetalePrecoverage X)
    (h : ∀ i, ResolutionLF ((ProEtale.upperStar Ab.{u + 1} (U.f i)).obj R)
      (((ProEtale.upperStar Ab.{u + 1} (U.f i)).mapMod R).obj M)) : ResolutionLF R M := by
  choose V hV using h
  refine ⟨U.bind V, fun ij ↦ ?_⟩
  rcases ij with ⟨i, j⟩
  exact (free_pullback_comp_iff ((V i).f j) (U.f i) M).mpr (hV i j)

private lemma resolutionLF_of_free {X : Scheme.{u}}
    {R : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}} [MonObj R]
    {M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) R}
    (h : Mod.IsFree R M) : ResolutionLF R M := by
  exact ⟨.singleton (𝟙 _) (Precoverage.mem_coverings_of_isIso _),
    fun _ ↦ free_pullback _ h⟩

private lemma resolutionLF_of_comap {X : Scheme.{u}}
    {R S : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}}
    [MonObj R] [MonObj S] [IsCommMonObj R] [IsCommMonObj S]
    (φ : R ⟶ S) [IsMonHom φ] [IsIso φ]
    {M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) S}
    (h : ResolutionLF R ((Mod.comap φ).obj M)) : ResolutionLF S M := by
  exact locally_free_of_iso (locally_free_comap (inv φ) h)
    ((Mod.comapEquivalenceOfIsIso φ).unitIso.app M).symm

private lemma resolutionFreeZero {X : Scheme.{u}}
    (R : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) [MonObj R] :
    Mod.IsFree R (0 : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) R) := by
  refine ⟨0, ⟨(isZero_zero _).iso ((IsZero.iff_id_eq_zero _).mpr ?_)⟩⟩
  apply biproduct.hom_ext
  intro i
  exact Fin.elim0 i

private lemma resolutionFreeRegular {X : Scheme.{u}}
    (R : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) [MonObj R] :
    Mod.IsFree R (Mod.regular R) :=
  ⟨1, ⟨(biproductUniqueIso (fun _ : Fin 1 ↦ Mod.regular R)).symm⟩⟩

private lemma resolutionLF_biprod {X : Scheme.{u}}
    {R : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}} [MonObj R]
    {M N : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) R}
    (hM : Mod.IsFree R M) (hN : ResolutionLF R N) : ResolutionLF R (M ⊞ N) := by
  obtain ⟨U, hU⟩ := hN
  refine ⟨U, fun i ↦ ?_⟩
  let F := (ProEtale.upperStar Ab.{u + 1} (U.f i)).mapMod R
  exact free_of_iso (free_biprod (free_pullback (U.f i) hM) (hU i))
    (F.mapBiprod M N).symm

-- The pivot cover decreases source rank and preserves the rational cokernel condition.
private lemma resolutionMatrixImage (ℓ : ℕ) [Fact ℓ.Prime]
    (E : Type) [NormedField E] [NormedAlgebra ℚ_[ℓ] E] :
    ∀ (n : ℕ) (X : Scheme.{u})
      (A B : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
        (condensedRingObj (integralCoeff ℓ E) X)) (a : A ⟶ B),
      Nonempty (A ≅ Mod.finiteFree (condensedRingObj (integralCoeff ℓ E) X) n) →
      Mod.IsFree (condensedRingObj (integralCoeff ℓ E) X) B →
      RationalCokernelFree ℓ E a →
      ResolutionLF (condensedRingObj (integralCoeff ℓ E) X) (image a) := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n IH =>
    intro X A B a hA hB hLF
    obtain ⟨V, hV⟩ := integralMatrix_pivot_cover ℓ E n X A B a hA hB hLF
    apply resolutionLF_of_cover V
    intro k
    let R := condensedRingObj (integralCoeff ℓ E) X
    let R' := condensedRingObj (integralCoeff ℓ E) (V.X k)
    let F := (ProEtale.upperStar Ab.{u + 1} (V.f k)).mapMod R
    let α := condensedPullbackHom (integralCoeff ℓ E) (V.f k)
    let J := Mod.comap (D := Sheaf (Scheme.ProEt.topology (V.X k)) Ab.{u + 1}) (inv α)
    let T := F ⋙ J
    have hT : ResolutionLF R' (image (T.map a)) := by
      rcases hV k with hz | ⟨m, hmn, A₁, B₁, iA, hB₁, p, hp, hunit, r, c, d, eA, eB, he⟩
      · rw [show T.map a = 0 from hz]
        exact locally_free_of_iso (resolutionLF_of_free (resolutionFreeZero R')) imageZero.symm
      · let _ := hp
        let b := biprod.lift (biprod.desc p (r ≫ p)) (biprod.desc c d)
        let eC : cokernel (T.map a) ≅ cokernel b :=
          cokernel.mapIso (T.map a) b eA eB (by
            dsimp only [b]
            rw [← he]
            simp only [Iso.hom_inv_id_assoc]
            rfl)
        let L := Mod.extendScalars (coefficientMap (integralScalarMap ℓ E) (V.X k))
        have : IsIso (L.map p) := hunit
        let eS := L.mapIso eC ≪≫ mappedPivotCokernelIso L p r c d
        have hS : RationalCokernelFree ℓ E (d - r ≫ c) :=
          locally_free_of_iso (rationalCokernelFree_pullback ℓ E (V.f k) a hLF) eS
        have hI := IH m hmn (V.X k) A₁ B₁ (d - r ≫ c) ⟨iA⟩ hB₁ hS
        let eI : image (T.map a) ≅ image b :=
          resolutionImageIso (T.map a) b eA eB (by
            dsimp only [b]
            rw [← he]
            simp only [Iso.hom_inv_id_assoc]
            rfl)
        exact locally_free_of_iso
          (resolutionLF_biprod (resolutionFreeRegular R') hI)
          ((pivotImageIso p r c d).symm ≪≫ eI.symm)
    have hJ := locally_free_of_iso hT (PreservesImage.iso J (F.map a))
    have hF := resolutionLF_of_comap (inv α) hJ
    exact locally_free_of_iso hF (PreservesImage.iso F a)

private lemma resolutionCommonFreeFP {X : Scheme.{u}}
    {R : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}} [MonObj R] [IsCommMonObj R]
    {M N : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) R}
    (hM : ResolutionLF R M) (hN : IsLocallyFinitelyPresented R N) :
    ∃ U : Scheme.Cover.{u} Scheme.proetalePrecoverage X, ∀ i,
      Mod.IsFree ((ProEtale.upperStar Ab.{u + 1} (U.f i)).obj R)
        (((ProEtale.upperStar Ab.{u + 1} (U.f i)).mapMod R).obj M) ∧
      Mod.IsFinitelyPresented ((ProEtale.upperStar Ab.{u + 1} (U.f i)).obj R)
        (((ProEtale.upperStar Ab.{u + 1} (U.f i)).mapMod R).obj N) := by
  obtain ⟨U, hU⟩ := hM
  obtain ⟨V, hV⟩ := hN
  refine ⟨U.bind (fun i ↦ V.pullback₁ (U.f i)), fun ij ↦ ?_⟩
  rcases ij with ⟨i, j⟩
  constructor
  · exact (free_pullback_comp_iff (pullback.fst (U.f i) (V.f j)) (U.f i) M).mpr
      (free_pullback (pullback.fst (U.f i) (V.f j)) (hU i))
  · change Mod.IsFinitelyPresented
      ((ProEtale.upperStar Ab.{u + 1} (pullback.fst (U.f i) (V.f j) ≫ U.f i)).obj R)
      (((ProEtale.upperStar Ab.{u + 1}
        (pullback.fst (U.f i) (V.f j) ≫ U.f i)).mapMod R).obj N)
    rw [pullback.condition]
    exact (fp_pullback_comp_iff (pullback.snd (U.f i) (V.f j)) (V.f j) N).mpr
      (fp_pullback (pullback.snd (U.f i) (V.f j)) (hV j))

private lemma resolutionKernelLF (ℓ : ℕ) [Fact ℓ.Prime]
    (E : Type) [NormedField E] [NormedAlgebra ℚ_[ℓ] E]
    [FiniteDimensional ℚ_[ℓ] E]
    (X : Scheme.{u}) [TopologicalSpace.NoetherianSpace X]
    {F₀ P : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (integralCoeff ℓ E) X)}
    (g : F₀ ⟶ P) [Epi g]
    (hF : ResolutionLF (condensedRingObj (integralCoeff ℓ E) X) F₀)
    (hP : IsLocallyFinitelyPresented (condensedRingObj (integralCoeff ℓ E) X) P) :
    ResolutionLF (condensedRingObj (integralCoeff ℓ E) X) (kernel g) := by
  let R := condensedRingObj (integralCoeff ℓ E) X
  have hFfp : IsLocallyFinitelyPresented R F₀ := by
    obtain ⟨U, hU⟩ := hF
    exact ⟨U, fun i ↦ fp_of_free (hU i)⟩
  have hmat : RationalMatrixKernels.{u} ℓ E := rationalMatrixKernels_of_integral ℓ E
    (integralMatrixKernels_of_pivots ℓ E (integralMatrix_pivot_cover ℓ E))
  have hK : IsLocallyFinitelyPresented R (kernel g) :=
    integral_lfp_kernel_of_rational ℓ E hmat X g hFfp hP
  have hPE := resolutionRationalLF ℓ E X P hP
  have hCE : RationalCokernelFree ℓ E (0 : P ⟶ P) :=
    locally_free_of_iso hPE
      ((Mod.extendScalars (coefficientMap (integralScalarMap ℓ E) X)).mapIso
        cokernelZeroIsoTarget.symm)
  obtain ⟨U, hU⟩ := resolutionCommonFreeFP hF hK
  apply resolutionLF_of_cover U
  intro i
  let R' := condensedRingObj (integralCoeff ℓ E) (U.X i)
  let F := (ProEtale.upperStar Ab.{u + 1} (U.f i)).mapMod R
  let α := condensedPullbackHom (integralCoeff ℓ E) (U.f i)
  let J := Mod.comap (D := Sheaf (Scheme.ProEt.topology (U.X i)) Ab.{u + 1}) (inv α)
  let T : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) R ⥤
      Mod (Sheaf (Scheme.ProEt.topology (U.X i)) Ab.{u + 1}) R' := F ⋙ J
  have : PreservesFiniteLimits T := inferInstance
  have : PreservesFiniteColimits T := inferInstance
  have : T.Additive := inferInstance
  have hTKfp : Mod.IsFinitelyPresented R' (T.obj (kernel g)) :=
    fp_comap (inv α) (hU i).2
  obtain ⟨n, m, a, ⟨ea⟩⟩ := hTKfp
  let π : Mod.finiteFree R' n ⟶ T.obj (kernel g) := cokernel.π a ≫ ea.inv
  have : Epi π := by dsimp only [π]; infer_instance
  let δ : Mod.finiteFree R' n ⟶ T.obj F₀ := π ≫ T.map (kernel.ι g)
  have : Mono (T.map (kernel.ι g)) := inferInstance
  let ei : image δ ≅ T.obj (kernel g) :=
    (image.isoStrongEpiMono π (T.map (kernel.ι g)) rfl).symm
  let eP : cokernel (kernel.ι g) ≅ P :=
    colimit.isoColimitCocone ⟨_, Abelian.epiIsCokernelOfKernel _ (kernelIsKernel g)⟩
  let eδ : cokernel δ ≅ T.obj P :=
    cokernelEpiComp π (T.map (kernel.ι g)) ≪≫
      (PreservesCokernel.iso T (kernel.ι g)).symm ≪≫ T.mapIso eP
  let L := Mod.extendScalars (coefficientMap (integralScalarMap ℓ E) (U.X i))
  have hTR : ResolutionLF _ (L.obj (T.obj P)) := by
    have h := rationalCokernelFree_pullback ℓ E (U.f i) (0 : P ⟶ P) hCE
    let ez : cokernel (T.map (0 : P ⟶ P)) ≅ T.obj P :=
      cokernelIsoOfEq (T.map_zero _ _) ≪≫ cokernelZeroIsoTarget
    exact locally_free_of_iso h (L.mapIso ez)
  have hδ : RationalCokernelFree ℓ E δ :=
    locally_free_of_iso hTR (L.mapIso eδ.symm)
  have hI := resolutionMatrixImage ℓ E n (U.X i) (Mod.finiteFree R' n)
    (T.obj F₀) δ ⟨Iso.refl _⟩ (free_comap (inv α) (hU i).1) hδ
  have hTK := locally_free_of_iso hI ei
  exact resolutionLF_of_comap (inv α) hTK

private lemma resolutionLF_extension {X : Scheme.{u}}
    {R : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}} [MonObj R] [IsCommMonObj R]
    (S : ShortComplex (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) R))
    (hs : S.ShortExact) (h₁ : ResolutionLF R S.X₁) (h₃ : ResolutionLF R S.X₃) :
    ResolutionLF R S.X₂ := by
  obtain ⟨U, hU⟩ := common_free_cover h₁ h₃
  apply resolutionLF_of_cover U
  intro i
  let R' := (ProEtale.upperStar Ab.{u + 1} (U.f i)).obj R
  let F := (ProEtale.upperStar Ab.{u + 1} (U.f i)).mapMod R
  have hsF := hs.map_of_exact F
  have : Epi (F.map S.g) := hsF.epi_g
  obtain ⟨V, hV⟩ := freeEpiLocalSplitting (U.X i) R' _ _ (F.map S.g) (hU i).2
  refine ⟨V, fun j ↦ ?_⟩
  let G := (ProEtale.upperStar Ab.{u + 1} (V.f j)).mapMod R'
  have : IsSplitEpi (G.map (F.map S.g)) := hV j
  have hsG := hsF.map_of_exact G
  let split := ShortComplex.Splitting.ofExactOfSection _ hsG.exact
    (section_ (G.map (F.map S.g))) (IsSplitEpi.id _) hsG.mono_f
  exact free_of_iso
    (free_biprod (free_pullback (V.f j) (hU i).1) (free_pullback (V.f j) (hU i).2))
    split.isoBinaryBiproduct.symm

-- Pulling an epimorphism back preserves its kernel and yields a locally split extension.
private lemma resolutionLF_pullback {X : Scheme.{u}}
    {R : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}} [MonObj R] [IsCommMonObj R]
    {P Q B : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) R}
    (q : P ⟶ Q) [Epi q] (b : B ⟶ Q)
    (hK : ResolutionLF R (kernel q)) (hB : ResolutionLF R B) :
    ResolutionLF R (pullback q b) := by
  let v := pullback.snd q b
  let sq := (IsPullback.of_hasPullback q b).flip
  have : IsIso (kernel.map v q (pullback.fst q b) b sq.w) :=
    isIso_kernel_map_of_isPullback sq
  let e : kernel v ≅ kernel q := asIso (kernel.map v q (pullback.fst q b) b sq.w)
  have hV : ResolutionLF R (kernel v) := locally_free_of_iso hK e.symm
  exact resolutionLF_extension (ShortComplex.mk (kernel.ι v) v (kernel.condition v))
    { exact := ShortComplex.exact_kernel v } hV hB

end AlgebraicGeometry.ProEtale.CondensedRing

namespace AlgebraicGeometry.ProEtale

/-- A locally finitely presented integral coefficient module has a two-term locally free
resolution. Source: Bhatt--Scholze, Definition 6.8.10, Proposition 6.8.11(3),
Remark 7.3.2 and Lemma 7.3.9 (finite locally constant sheaves are classical).

Proof: choose N so the image I of multiplication by ℓ^N is locally finite free
and Q = P/ℓ^N P has a finite locally constant underlying sheaf of sets. Construct
B as the free module object on this sheaf of sets, using free abelian sheafification
followed by the free module-object functor. Their composite is left adjoint to the
faithful underlying-set functor, so its counit b : B → Q is epimorphic. Pullback
commutes with this free construction. Finite constant generators give a finite
biproduct of regular modules, so B is locally finite free.

Set F₀ = P ×_Q B. The projection to B is an epimorphism with kernel I. After a
common free cover, an epimorphism onto a finite free module locally splits by
lifting the finitely many basis sections. Thus F₀ is locally finite free. Its
projection g to P is epimorphic because b is. Its kernel is locally finitely
presented by the integral kernel theorem. On a common presentation cover, present
this kernel by a finite free module A and compose A → ker g with ker g → F₀.
The resulting finite matrix δ has image ker g and cokernel P. Rationalizing P is
locally finite free by the field finite-presentation theorem and noetherianity.

Prove local freeness of image δ by induction on its source rank, using the existing
integral pivot cover. The zero matrix has zero image. In the nonzero branch, row
elimination changes the pivot block to [p, 0; c, d-rc], with p monic and rationally
invertible. Its image is the direct sum of the regular module and image(d-rc), by
an explicit epi-mono factorization. Rational inversion of p identifies its rational
cokernel with that of d-rc, so induction applies at strictly smaller source rank.
Images commute with the exact coefficient-normalized pullback functors, and binding
the covers gives the required local freeness of ker g. Take F₁ = ker g and its
inclusion into F₀ to obtain the short exact sequence. The constructions include
rank zero and empty covers; no resolution object is defined by an unproved choice.
-/
theorem integral_lfp_locallyFree_resolution
    (X : Scheme.{u}) [TopologicalSpace.NoetherianSpace X]
    (ℓ : ℕ) [Fact ℓ.Prime] (E : Type) [NormedField E]
    [NormedAlgebra ℚ_[ℓ] E] [FiniteDimensional ℚ_[ℓ] E]
    (P : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (CondensedRing.integralCoeff ℓ E) X))
    (hP : IsLocallyFinitelyPresented
      (condensedRingObj (CondensedRing.integralCoeff ℓ E) X) P) :
    ∃ (F₁ F₀ : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
        (condensedRingObj (CondensedRing.integralCoeff ℓ E) X))
      (f : F₁ ⟶ F₀) (g : F₀ ⟶ P) (w : f ≫ g = 0),
      (ShortComplex.mk f g w).ShortExact ∧
      (∃ C : Scheme.Cover.{u} Scheme.proetalePrecoverage X, ∀ s : C.I₀,
        Mod.IsFree ((upperStar Ab.{u + 1} (C.f s)).obj
          (condensedRingObj (CondensedRing.integralCoeff ℓ E) X))
          (((upperStar Ab.{u + 1} (C.f s)).mapMod _).obj F₁)) ∧
      (∃ C : Scheme.Cover.{u} Scheme.proetalePrecoverage X, ∀ s : C.I₀,
        Mod.IsFree ((upperStar Ab.{u + 1} (C.f s)).obj
          (condensedRingObj (CondensedRing.integralCoeff ℓ E) X))
          (((upperStar Ab.{u + 1} (C.f s)).mapMod _).obj F₀)) := by
  open CondensedRing in
  obtain ⟨N, hI, hB⟩ := integral_lfp_eventual_free_image X ℓ E P hP
  let R := condensedRingObj (CondensedRing.integralCoeff ℓ E) X
  let a := (ℓ ^ N) • 𝟙 P
  let q := cokernel.π a
  let B := moduleObjectFreeGenerators R (cokernel a)
  let b : B ⟶ cokernel a := moduleObjectFreeGeneratorsπ R (cokernel a)
  have : Epi q := by dsimp only [q]; infer_instance
  have : Epi b := by dsimp only [b]; infer_instance
  have hKq : CondensedRing.ResolutionLF R (kernel q) :=
    locally_free_of_iso hI (Abelian.imageIsoImage a).symm
  have hF₀ := CondensedRing.resolutionLF_pullback q b hKq hB
  let g := pullback.fst q b
  have : Epi g := by dsimp only [g]; infer_instance
  have hF₁ := CondensedRing.resolutionKernelLF ℓ E X g hF₀ hP
  exact ⟨kernel g, pullback q b, kernel.ι g, g, kernel.condition g,
    { exact := ShortComplex.exact_kernel g }, hF₁, hF₀⟩

end AlgebraicGeometry.ProEtale
