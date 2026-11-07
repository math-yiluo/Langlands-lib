import Langlands.AlgebraicGeometry.Modules.FiniteSupportSectionsDecomposition
import Langlands.Cohomology.RightDerivedAdditive
import Langlands.AlgebraicGeometry.Modules.HigherDirectImageOpenRestriction
import Langlands.AlgebraicGeometry.Modules.FiniteClosedSupportLerayProof
import Langlands.AlgebraicGeometry.Modules.LineBundleFiniteFreeEulerProof
import Langlands.AlgebraicGeometry.Modules.PullbackMonoidal
import Langlands.AlgebraicGeometry.Modules.TensorPowerDistributivity
import Langlands.AlgebraicGeometry.Picard.LineBundlePullback
import Langlands.AlgebraicGeometry.Modules.EulerCharacteristicBasicProof

/-! # Twisting by a locally free module pulled back from a base with finite support -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite TopologicalSpace

namespace Langlands.AlgebraicGeometry.Modules.DerivedSections

open Langlands.Scheme.Modules Langlands.AlgebraicGeometry.Picard

variable {Y Z : Scheme.{u}}

/-- Restriction along an open immersion commutes with the tensor product. -/
def restrictTensorIso' {U : Scheme.{u}} (j : U ⟶ Z) [IsOpenImmersion j] (M N : Z.Modules) :
    (Scheme.Modules.restrictFunctor j).obj (tensorObj M N) ≅
      tensorObj ((Scheme.Modules.restrictFunctor j).obj M)
        ((Scheme.Modules.restrictFunctor j).obj N) :=
  (Scheme.Modules.restrictFunctorIsoPullback j).app _ ≪≫ pullbackTensorIso j M N ≪≫
    tensorMapIso ((Scheme.Modules.restrictFunctorIsoPullback j).app M).symm
      ((Scheme.Modules.restrictFunctorIsoPullback j).app N).symm

set_option backward.isDefEq.respectTransparency false in
/-- The pullback of the free module on `d` generators is free on `d` generators. -/
def pullbackFreeIso {X : Scheme.{u}} (f : X ⟶ Y) (d : ℕ) :
    (Scheme.Modules.pullback f).obj
        (SheafOfModules.free (R := Y.ringCatSheaf) (ULift.{u} (Fin d))) ≅
      SheafOfModules.free (R := X.ringCatSheaf) (ULift.{u} (Fin d)) :=
by
  have : (Scheme.Modules.pullback f).IsLeftAdjoint :=
    (Scheme.Modules.pullbackPushforwardAdjunction f).isLeftAdjoint
  let : PreservesColimitsOfSize.{u, u} (Scheme.Modules.pullback f) := inferInstance
  exact (SheafOfModules.mapFreeIso (Scheme.Modules.pullback f) (ULift.{u} (Fin d))
    (pullbackUnitIso f).symm).symm

variable (p : Z ⟶ Y) (F : LineBundle Z) (W : Y.Modules) (d : ℕ)

/-- Over an open `V` on which `W` is free of rank `d`, the restriction of
`Rⁿ p_*(F ⊗ p^* W)` is a coproduct of `d` copies of the restriction of `Rⁿ p_* F`. -/
def twistRestrictIso (V : Y.Opens)
    (eV : (Scheme.Modules.restrictFunctor V.ι).obj W ≅
      SheafOfModules.free (R := V.toScheme.ringCatSheaf) (ULift.{u} (Fin d))) (n : ℕ) :
    (Scheme.Modules.restrictFunctor V.ι).obj
        ((higherDirectImage p n).obj (tensorObj F.obj ((Scheme.Modules.pullback p).obj W))) ≅
      ∐ (fun _ : Fin d => (Scheme.Modules.restrictFunctor V.ι).obj
        ((higherDirectImage p n).obj F.obj)) := by
  let j := (p ⁻¹ᵁ V).ι
  let F' : LineBundle (p ⁻¹ᵁ V) := (LineBundle.pullback j).obj F
  have : (higherDirectImage (p ∣_ V) n).Additive :=
    CechResolution.rightDerived_additive (Scheme.Modules.pushforward (p ∣_ V)) n
  exact (higherDirectImageRestrictIso p V _ n).symm ≪≫
    (higherDirectImage (p ∣_ V) n).mapIso
      (restrictTensorIso' j _ _ ≪≫
        tensorMapIso ((Scheme.Modules.restrictFunctorIsoPullback j).app F.obj)
          (restrictPullbackIso p V W ≪≫ (Scheme.Modules.pullback (p ∣_ V)).mapIso eV ≪≫
            pullbackFreeIso (p ∣_ V) d) ≪≫
        lineBundleFiniteFreeTensorIso F' d) ≪≫
    PreservesCoproduct.iso (higherDirectImage (p ∣_ V) n) (fun _ : Fin d => F'.obj) ≪≫
    Sigma.mapIso (fun _ => (higherDirectImage (p ∣_ V) n).mapIso
      ((Scheme.Modules.restrictFunctorIsoPullback j).app F.obj).symm ≪≫
        higherDirectImageRestrictIso p V F.obj n)

/-- Relative global sections of a coproduct of `d` copies of a module are `d`-tuples of
sections. -/
def relativeGlobalSectionsCoproductIso {T : Scheme.{u}} {R : CommRingCat.{u}} (t : T ⟶ Spec R)
    (M : T.Modules) :
    (relativeGlobalSections t).obj (∐ fun _ : Fin d => M) ≅
      ModuleCat.of R (Fin d → (relativeGlobalSections t).obj M) :=
  PreservesCoproduct.iso (relativeGlobalSections t) (fun _ : Fin d => M) ≪≫
    (biproduct.isoCoproduct (fun _ : Fin d => (relativeGlobalSections t).obj M)).symm ≪≫
    ModuleCat.biproductIsoPi _

/-- A coproduct of zero objects is a zero object. -/
lemma isZero_sigma_of_isZero {T : Scheme.{u}} (M : Fin d → T.Modules) (h : ∀ i, IsZero (M i)) :
    IsZero (∐ M) := by
  rw [IsZero.iff_id_eq_zero]
  exact Sigma.hom_ext _ _ fun i => (h i).eq_of_src _ _

/-- A free chart over `V` restricts to a free chart over every smaller open `V'`. -/
def restrictFreeOfLE {V V' : Y.Opens} (h : V' ≤ V)
    (eV : (Scheme.Modules.restrictFunctor V.ι).obj W ≅
      SheafOfModules.free (R := V.toScheme.ringCatSheaf) (ULift.{u} (Fin d))) :
    (Scheme.Modules.restrictFunctor V'.ι).obj W ≅
      SheafOfModules.free (R := V'.toScheme.ringCatSheaf) (ULift.{u} (Fin d)) :=
  (Scheme.Modules.restrictFunctorCongr (Y.homOfLE_ι h).symm).app W ≪≫
    (Scheme.Modules.restrictFunctorComp (Y.homOfLE h) V.ι).app W ≪≫
    (Scheme.Modules.restrictFunctor (Y.homOfLE h)).mapIso eV ≪≫
    restrictFiniteFreeIso (Y.homOfLE h) d

/-- A module whose stalks vanish at every point of an open `O` restricts to zero on `O`. -/
lemma isZero_restrict_of_stalkSupport (G : Y.Modules) (O : Y.Opens)
    (hO : ∀ y ∈ O, y ∉ stalkSupport G) :
    IsZero ((Scheme.Modules.restrictFunctor O.ι).obj G) := by
  rw [isZero_iff_forall_isZero_stalk]
  intro z
  have h := hO z.1 z.2
  rw [mem_stalkSupport, not_not] at h
  exact h.of_iso ((Scheme.Modules.restrictStalkNatIso O.ι z).app G)

/-- If the restriction of a module to an open `O` is zero, its stalks vanish on `O`. -/
lemma not_mem_stalkSupport_of_isZero_restrict (G : Y.Modules) (O : Y.Opens)
    (h : IsZero ((Scheme.Modules.restrictFunctor O.ι).obj G)) (y : Y) (hy : y ∈ O) :
    y ∉ stalkSupport G := by
  rw [mem_stalkSupport, not_not]
  have h1 : IsZero ((Scheme.Modules.toPresheaf _ ⋙
      TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} (⟨y, hy⟩ : O)).obj
        ((Scheme.Modules.restrictFunctor O.ι).obj G)) :=
    (Scheme.Modules.toPresheaf _ ⋙
      TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} (⟨y, hy⟩ : O)).map_isZero h
  exact h1.of_iso ((Scheme.Modules.restrictStalkNatIso O.ι ⟨y, hy⟩).app G).symm

/-- The stalk support of a module with finite closed support is closed. -/
lemma isClosed_stalkSupport_of_hasFiniteClosedSupport {G : Y.Modules}
    (h : HasFiniteClosedSupport G) : IsClosed (stalkSupport G) := by
  have := h.1.isClosed_biUnion (f := fun x => ({x} : Set Y)) fun x hx => h.2 x hx
  simpa only [Set.biUnion_of_singleton] using this

/-- Twisting by a module with free charts of rank `d` does not enlarge the support of the
higher direct images. -/
theorem stalkSupport_twist_subset
    (hW : ∀ y : Y, ∃ V : Y.Opens, y ∈ V ∧
      Nonempty ((Scheme.Modules.restrictFunctor V.ι).obj W ≅
        SheafOfModules.free (R := V.toScheme.ringCatSheaf) (ULift.{u} (Fin d))))
    (n : ℕ) (hsupp : HasFiniteClosedSupport ((higherDirectImage p n).obj F.obj)) :
    stalkSupport ((higherDirectImage p n).obj
        (tensorObj F.obj ((Scheme.Modules.pullback p).obj W))) ⊆
      stalkSupport ((higherDirectImage p n).obj F.obj) := by
  intro y hy
  by_contra hyG
  obtain ⟨V, hyV, ⟨eV⟩⟩ := hW y
  let O : Y.Opens := ⟨(stalkSupport ((higherDirectImage p n).obj F.obj))ᶜ,
    (isClosed_stalkSupport_of_hasFiniteClosedSupport hsupp).isOpen_compl⟩
  let V' : Y.Opens := V ⊓ O
  have hz : IsZero ((Scheme.Modules.restrictFunctor V'.ι).obj
      ((higherDirectImage p n).obj F.obj)) :=
    isZero_restrict_of_stalkSupport _ V' fun z hz => hz.2
  have hz' := (isZero_sigma_of_isZero d _ fun _ => hz).of_iso
    (twistRestrictIso p F W d V' (restrictFreeOfLE W d inf_le_left eV) n)
  exact not_mem_stalkSupport_of_isZero_restrict _ V' hz' y ⟨hyV, hyG⟩ hy

/-- **Twisting by a locally free module of rank `d` from the base.** Let `p : Z ⟶ Y` and
`s : Y ⟶ Spec K`, let `F` be a line bundle on `Z` whose higher direct images along `p` all have
finite closed support, and let `W` be a module on `Y` with free charts of rank `d`. If
`Hⁿ(Z, F)` is finite dimensional, then so is `Hⁿ(Z, F ⊗ p^* W)`, of `d` times the dimension. -/
theorem finrank_cohomology_twist {K : Type u} [Field K] (s : Y ⟶ Spec (CommRingCat.of K))
    (hW : ∀ y : Y, ∃ V : Y.Opens, y ∈ V ∧
      Nonempty ((Scheme.Modules.restrictFunctor V.ι).obj W ≅
        SheafOfModules.free (R := V.toScheme.ringCatSheaf) (ULift.{u} (Fin d))))
    (hsupp : ∀ q, HasFiniteClosedSupport ((higherDirectImage p q).obj F.obj)) (n : ℕ)
    (hfin : Module.Finite K ((relativeCohomology (p ≫ s) n).obj F.obj)) :
    Module.Finite K ((relativeCohomology (p ≫ s) n).obj
        (tensorObj F.obj ((Scheme.Modules.pullback p).obj W))) ∧
      Module.finrank K ((relativeCohomology (p ≫ s) n).obj
          (tensorObj F.obj ((Scheme.Modules.pullback p).obj W))) =
        d * Module.finrank K ((relativeCohomology (p ≫ s) n).obj F.obj) := by
  classical
  let T := tensorObj F.obj ((Scheme.Modules.pullback p).obj W)
  let G := (higherDirectImage p n).obj F.obj
  let G' := (higherDirectImage p n).obj T
  have hsupp' : ∀ q, HasFiniteClosedSupport ((higherDirectImage p q).obj T) := fun q =>
    HasFiniteClosedSupport.of_subset (hsupp q).1 (hsupp q).2
      (stalkSupport_twist_subset p F W d hW q (hsupp q))
  obtain ⟨eF⟩ := finiteClosedSupportLeray Z Y (CommRingCat.of K) p s F.obj hsupp n
  obtain ⟨eT⟩ := finiteClosedSupportLeray Z Y (CommRingCat.of K) p s T hsupp' n
  let S : Finset Y := (hsupp n).1.toFinset
  have hScl : ∀ x ∈ S, IsClosed ({x} : Set Y) := fun x hx =>
    (hsupp n).2 x ((hsupp n).1.mem_toFinset.mp hx)
  have hGS : stalkSupport G ⊆ S := fun x hx => (hsupp n).1.mem_toFinset.mpr hx
  have hG'S : stalkSupport G' ⊆ S :=
    (stalkSupport_twist_subset p F W d hW n (hsupp n)).trans hGS
  choose V0 hV0 eV0 using hW
  let C : Y → Y.Opens := fun x => ⟨((S.erase x : Finset Y) : Set Y)ᶜ,
    (isClosed_finset_of_isClosed_singleton (S.erase x)
      fun z hz => hScl z (Finset.mem_of_mem_erase hz)).isOpen_compl⟩
  let V : Y → Y.Opens := fun x => V0 x ⊓ C x
  have hV : ∀ x ∈ S, x ∈ V x := fun x _ => ⟨hV0 x, by simp [C]⟩
  have hVS : ∀ x ∈ S, ∀ y ∈ S, y ∈ V x → y = x := fun x _ y hy hyV => by
    by_contra hne
    exact hyV.2 (Finset.mem_erase.mpr ⟨hne, hy⟩)
  let eV : ∀ x, (Scheme.Modules.restrictFunctor (V x).ι).obj W ≅
      SheafOfModules.free (R := (V x).toScheme.ringCatSheaf) (ULift.{u} (Fin d)) := fun x =>
    restrictFreeOfLE W d inf_le_left (eV0 x).some
  let LG := LinearEquiv.ofBijective _ (sectionsRestrictPi_bijective s G S hScl hGS V hV hVS)
  let LG' := LinearEquiv.ofBijective _ (sectionsRestrictPi_bijective s G' S hScl hG'S V hV hVS)
  let loc : ∀ x : S, (relativeGlobalSections ((V x).ι ≫ s)).obj
      ((Scheme.Modules.restrictFunctor (V x).ι).obj G') ≃ₗ[K]
        (Fin d → (relativeGlobalSections ((V x).ι ≫ s)).obj
          ((Scheme.Modules.restrictFunctor (V x).ι).obj G)) := fun x =>
    ((relativeGlobalSections ((V x).ι ≫ s)).mapIso (twistRestrictIso p F W d (V x) (eV x) n) ≪≫
      relativeGlobalSectionsCoproductIso d _ _).toLinearEquiv
  have hΓ : Module.Finite K ((relativeGlobalSections s).obj G) :=
    Module.Finite.equiv eF.toLinearEquiv
  have hcomp : ∀ x : S, Module.Finite K ((relativeGlobalSections ((V x).ι ≫ s)).obj
      ((Scheme.Modules.restrictFunctor (V x).ι).obj G)) := fun x =>
    Module.Finite.of_surjective ((LinearMap.proj x).comp LG.toLinearMap)
      ((Function.surjective_eval x).comp LG.surjective)
  let E := eT.toLinearEquiv ≪≫ₗ LG' ≪≫ₗ LinearEquiv.piCongrRight loc
  have hpi : Module.Finite K (∀ x : S, Fin d → (relativeGlobalSections ((V x).ι ≫ s)).obj
      ((Scheme.Modules.restrictFunctor (V x).ι).obj G)) := Module.Finite.pi
  refine ⟨Module.Finite.equiv E.symm, ?_⟩
  rw [E.finrank_eq, eF.toLinearEquiv.finrank_eq, LG.finrank_eq, Module.finrank_pi_fintype,
    Module.finrank_pi_fintype, Finset.mul_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Module.finrank_pi_fintype]
  simp

/-- **Euler characteristic of a twist by a locally free module of rank `d` from the base.**
Under the hypotheses of `finrank_cohomology_twist`, if `F` has finite cohomology then so has
`F ⊗ p^* W`, and `χ(F ⊗ p^* W) = d · χ(F)`. -/
theorem eulerCharacteristic_twist {K : Type u} [Field K] (s : Y ⟶ Spec (CommRingCat.of K))
    (hW : ∀ y : Y, ∃ V : Y.Opens, y ∈ V ∧
      Nonempty ((Scheme.Modules.restrictFunctor V.ι).obj W ≅
        SheafOfModules.free (R := V.toScheme.ringCatSheaf) (ULift.{u} (Fin d))))
    (hsupp : ∀ q, HasFiniteClosedSupport ((higherDirectImage p q).obj F.obj))
    (hF : HasFiniteCohomology (p ≫ s) F.obj) :
    HasFiniteCohomology (p ≫ s) (tensorObj F.obj ((Scheme.Modules.pullback p).obj W)) ∧
      ∀ hT : HasFiniteCohomology (p ≫ s)
          (tensorObj F.obj ((Scheme.Modules.pullback p).obj W)),
        eulerCharacteristic (p ≫ s) (tensorObj F.obj ((Scheme.Modules.pullback p).obj W)) hT =
          (d : ℤ) * eulerCharacteristic (p ≫ s) F.obj hF := by
  have h := fun n => finrank_cohomology_twist p F W d s hW hsupp n (hF.1 n)
  obtain ⟨N, hN⟩ := hF.2
  have hzero : ∀ n, N ≤ n → Module.finrank K ((relativeCohomology (p ≫ s) n).obj F.obj) = 0 :=
    fun n hn => by
      have : Subsingleton ((relativeCohomology (p ≫ s) n).obj F.obj) :=
        ModuleCat.subsingleton_of_isZero (hN n hn)
      exact Module.finrank_zero_of_subsingleton
  have hTzero : ∀ n, N ≤ n → IsZero ((relativeCohomology (p ≫ s) n).obj
      (tensorObj F.obj ((Scheme.Modules.pullback p).obj W))) := fun n hn => by
    have := (h n).1
    have h0 : Module.finrank K ((relativeCohomology (p ≫ s) n).obj
        (tensorObj F.obj ((Scheme.Modules.pullback p).obj W))) = 0 := by
      rw [(h n).2, hzero n hn, mul_zero]
    have : Subsingleton ((relativeCohomology (p ≫ s) n).obj
        (tensorObj F.obj ((Scheme.Modules.pullback p).obj W))) := Module.finrank_zero_iff.mp h0
    exact ModuleCat.isZero_of_subsingleton _
  have hT : HasFiniteCohomology (p ≫ s) (tensorObj F.obj ((Scheme.Modules.pullback p).obj W)) :=
    ⟨fun n => (h n).1, N, hTzero⟩
  refine ⟨hT, fun hT' => ?_⟩
  rw [eulerCharacteristic_eq_sum_range (p ≫ s) _ hT' N hTzero,
    eulerCharacteristic_eq_sum_range (p ≫ s) _ hF N hN, Finset.mul_sum]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [(h n).2]
  push_cast
  ring

end Langlands.AlgebraicGeometry.Modules.DerivedSections
