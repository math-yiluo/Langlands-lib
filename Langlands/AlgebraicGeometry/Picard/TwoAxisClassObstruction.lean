import Langlands.AlgebraicGeometry.Picard.TwoAxisClassArtinianLiftingProof
import Langlands.AlgebraicGeometry.Picard.OpennessOfVersality.Sufficiency
import Langlands.AlgebraicGeometry.Picard.OpennessOfVersality.NecessityGluing

/-! # Lifting two-axis classes along square-zero extensions and Čech obstruction cocycles

For the self-product of an abelian scheme over a test ring `Λ`, a lift of a two-axis class
along a square-zero extension exists if and only if a Čech one-cochain solves the cocycle
equation `d c + φ_* z = 0` of the Library's obstruction cochain `z`.
-/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open scoped TensorProduct

noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace Langlands.AlgebraicGeometry.Picard

open Langlands.Scheme.Modules Langlands.AbelianScheme

namespace TwoAxisRigidifiedLineBundle

open TwoAxisFamily UnramifiedFunctor OpennessOfVersality RelativeAffineSections

variable {S : Scheme.{u}} (A : Langlands.AbelianScheme S)
variable {Λ : Type u} [CommRing Λ] (f : Spec (CommRingCat.of Λ) ⟶ S)

instance : IsProper (productStructure A f) := by
  change IsProper (Limits.pullback.fst (abelian A (Over.mk f)).X.hom
    (abelian A (Over.mk f)).X.hom ≫ (abelian A (Over.mk f)).X.hom)
  infer_instance

/-- The carrier line bundle of a rigidified line bundle. -/
abbrev carrierBundle {T : Over S} (L : relative A T) :
    LineBundle (mumfordProduct (abelian A T)).left :=
  ⟨L.obj.carrier, L.property⟩

/-- A line bundle on the self-product over `B`, moved to the relative space of `B`. -/
abbrev toRel (B : Type u) [CommRing B] [Algebra Λ B]
    (L : LineBundle (mumfordProduct (abelian A (algebraOver f B))).left) :
    LineBundle (relSpace (productStructure A f) B) :=
  (LineBundle.pullback (inv (affineComparison A f B))).obj L

/-- Moving to the relative space commutes with pullback along an algebra map. -/
def toRelPullbackIso {B C : Type u} [CommRing B] [Algebra Λ B] [CommRing C] [Algebra Λ C]
    (φ : B →ₐ[Λ] C) (L : LineBundle (mumfordProduct (abelian A (algebraOver f B))).left) :
    (LineBundle.pullback (relMap (productStructure A f) φ)).obj (toRel A f B L) ≅
      toRel A f C ((LineBundle.pullback (productMap A (algHomOver f φ))).obj L) :=
  LineBundle.pullbackCompEqIso (relMap (productStructure A f) φ) (inv (affineComparison A f B))
      (inv_affineComparison_naturality A f φ) L ≪≫
    (LineBundle.pullbackCompEqIso (inv (affineComparison A f C))
      (productMap A (algHomOver f φ)) rfl L).symm

/-- Pulling back a line bundle of the relative space to the self-product commutes with pullback
along an algebra map. -/
def ofRelPullbackIso {B C : Type u} [CommRing B] [Algebra Λ B] [CommRing C] [Algebra Λ C]
    (φ : B →ₐ[Λ] C) (N : LineBundle (relSpace (productStructure A f) B)) :
    (LineBundle.pullback (productMap A (algHomOver f φ))).obj
        ((LineBundle.pullback (affineComparison A f B)).obj N) ≅
      (LineBundle.pullback (affineComparison A f C)).obj
        ((LineBundle.pullback (relMap (productStructure A f) φ)).obj N) :=
  LineBundle.pullbackCompEqIso (productMap A (algHomOver f φ)) (affineComparison A f B)
      (affineComparison_naturality A f φ).symm N ≪≫
    (LineBundle.pullbackCompEqIso (affineComparison A f C) (relMap (productStructure A f) φ)
      rfl N).symm

/-- A line bundle on the self-product is recovered from its relative-space version. -/
def ofRelToRelIso (B : Type u) [CommRing B] [Algebra Λ B]
    (L : LineBundle (mumfordProduct (abelian A (algebraOver f B))).left) :
    (LineBundle.pullback (affineComparison A f B)).obj (toRel A f B L) ≅ L :=
  LineBundle.pullbackCompEqIso (affineComparison A f B) (inv (affineComparison A f B))
      (IsIso.hom_inv_id _) L ≪≫ (LineBundle.pullbackId _).app L

/-- Equal restricted classes give isomorphic restricted carrier bundles. -/
lemma nonempty_carrierIso_of_eq {T U V : Over S} (h : V ⟶ T) (k : V ⟶ U) (L : relative A T)
    (L' : relative A U)
    (heq : classesPullback A h (Quotient.mk _ L) = classesPullback A k (Quotient.mk _ L')) :
    Nonempty ((LineBundle.pullback (productMap A h)).obj (carrierBundle A L) ≅
      (LineBundle.pullback (productMap A k)).obj (carrierBundle A L')) := by
  have h' : (Quotient.mk _ ((relativePullback A h).obj L) : Classes A V) =
      Quotient.mk _ ((relativePullback A k).obj L') := heq
  obtain ⟨φ⟩ := Quotient.exact h'
  exact ⟨(forget _ _ _ _ _).mapIso φ⟩

/-- A line bundle on the self-product over `B` whose restriction along `p` is isomorphic to the
carrier of a rigidified bundle `D₀` gives a class over `B` restricting to the class of `D₀`. -/
theorem exists_class_of_carrierIso {B C : Type u} [CommRing B] [Algebra Λ B] [CommRing C]
    [Algebra Λ C] (p : B →ₐ[Λ] C)
    (E : LineBundle (mumfordProduct (abelian A (algebraOver f B))).left)
    (D₀ : relative A (algebraOver f C))
    (e₀ : (LineBundle.pullback (productMap A (algHomOver f p))).obj E ≅ carrierBundle A D₀) :
    ∃ z : Classes A (algebraOver f B),
      classesPullback A (algHomOver f p) z = Quotient.mk _ D₀ := by
  let ρ := LineBundle.twoAxisNormalizedBundleRigidification pullbackTensorComparisonIsIso
    (abelian A (algebraOver f B)) E
  let eN := LineBundle.twoAxisNormalizedBundleRestrictionIso pullbackTensorComparisonIsIso
    (abelian A (algebraOver f B)) (abelian A (algebraOver f C))
    (productMap A (algHomOver f p)) (carrierMap A (algHomOver f p))
    (productMap_fst A _) (productMap_snd A _) (first_naturality A _) (second_naturality A _)
    E (carrierBundle A D₀) ((LineBundle.forget _).mapIso e₀)
    D₀.obj.rigidification.first.symm D₀.obj.rigidification.second.symm
  refine ⟨Quotient.mk _ (ofLineBundle _ ρ), ?_⟩
  change (Quotient.mk _ ((relativePullback A (algHomOver f p)).obj (ofLineBundle _ ρ)) :
      Classes A (algebraOver f C)) = Quotient.mk _ D₀
  exact Quotient.sound (nonempty_iso_of_carrierIso (abelian A (algebraOver f C)) eN)

omit [CommRing Λ] in
/-- Two `Λ`-algebra maps out of `Λ`-algebras agree after the structure maps from `Λ`. -/
lemma toAlgHom_comp_eq {Λ : Type u} [CommRing Λ] {B₁ B₂ C : Type u} [CommRing B₁]
    [Algebra Λ B₁] [CommRing B₂] [Algebra Λ B₂] [CommRing C] [Algebra Λ C]
    (χ : B₁ →ₐ[Λ] C) (q : B₂ →ₐ[Λ] C) :
    q.comp (IsScalarTower.toAlgHom Λ Λ B₂) = χ.comp (IsScalarTower.toAlgHom Λ Λ B₁) :=
  AlgHom.ext fun x => by simp

section Obstruction

variable {A₀ : Type u} [CommRing A₀] [Algebra Λ A₀]
  {Q : Type u} [AddCommGroup Q] [Module A₀ Q] [Module Λ Q] [IsScalarTower Λ A₀ Q]
  {M : Type u} [AddCommGroup M] [Module A₀ M] [Module Λ M] [IsScalarTower Λ A₀ M]
  (K : (relSpace (productStructure A f) Λ).OrderedAffineCover)
  (g : ∀ i j : K.ι, (Γ(relSpace (productStructure A f) Λ, K.U i ⊓ K.U j))ˣ)
  (hπ : Function.Surjective (algebraMap Λ A₀))
  (jQ : Q →ₗ[Λ] Λ) (hjQ : ∀ a : Λ, a ∈ RingHom.ker (algebraMap Λ A₀) ↔ ∃ x, jQ x = a)
  (hg : ∀ s : K.Idx 2, defect (productStructure A f) K g s ∈
    (RingHom.ker (algebraMap Λ A₀)).map
      (structureHom (productStructure A f) Λ (K.inter s)).hom)
  (L' : relative A (algebraOver f A₀))
  (e : ∀ i, Γ((toRel A f A₀ (carrierBundle A L')).obj,
    (testCover (productStructure A f) K A₀).U i))
  (he : ∀ i, Scheme.Modules.IsFrameOn (e i) ((testCover (productStructure A f) K A₀).U i))
  (hge : CocycleGluing.IsTransition e (pushUnits (productStructure A f) K
    (relMap (productStructure A f) (IsScalarTower.toAlgHom Λ Λ A₀))
    (testCover (productStructure A f) K A₀).U (fun _ _ => le_rfl) g))
  {Ã B : Type u} [CommRing Ã] [Algebra Λ Ã] [CommRing B] [Algebra Λ B]
  (χ : A₀ →ₐ[Λ] B) (q : Ã →ₐ[Λ] B) (hq : Function.Surjective q)
  (jM : M →ₗ[Λ] Ã) (hjMinj : Function.Injective jM)
  (hjMr : ∀ a, a ∈ RingHom.ker q.toRingHom ↔ ∃ m, jM m = a)
  (hjMsq : ∀ m m', jM m * jM m' = 0)

include he hge hq hjMsq in
/-- **A lift gives a cocycle.** If the restriction of the class of `L'` along `χ` lifts along
the square-zero extension `q` with kernel `M`, the obstruction cochain pushed by the
obstruction map `φ : Q → M` is a coboundary: `d c + φ_* z = 0`. -/
theorem exists_cocycle_of_classLift (hn : IsNilpotent (RingHom.ker q.toRingHom))
    (η : Classes A (algebraOver f Ã))
    (hη : classesPullback A (algHomOver f q) η =
      classesPullback A (algHomOver f χ) (Quotient.mk _ L')) :
    ∃ c : cplx (productStructure A f) K A₀ 1 ⊗[A₀] M,
      (dif (productStructure A f) K A₀ 1).rTensor M c +
        (phiQ χ q (toAlgHom_comp_eq χ q) hπ jQ (hjQ0_of jQ hjQ) jM hjMinj hjMr).lTensor
          (cplx (productStructure A f) K A₀ 2) (zObs (productStructure A f) K jQ hjQ g hg) =
        0 := by
  induction η using Quotient.inductionOn with
  | h Lη =>
  obtain ⟨φc⟩ := nonempty_carrierIso_of_eq A (algHomOver f q) (algHomOver f χ) Lη L' hη
  have hqρ := toAlgHom_comp_eq χ q
  let N := toRel A f Ã (carrierBundle A Lη)
  let φ : (LineBundle.pullback (relMap (productStructure A f) χ)).obj
        (toRel A f A₀ (carrierBundle A L')) ≅
      (LineBundle.pullback (relMap (productStructure A f) q)).obj N :=
    toRelPullbackIso A f χ (carrierBundle A L') ≪≫
      (LineBundle.pullback (inv (affineComparison A f B))).mapIso φc.symm ≪≫
      (toRelPullbackIso A f q (carrierBundle A Lη)).symm
  let φM := (LineBundle.forget _).mapIso φ
  obtain ⟨fr, hfr, hcoord⟩ := exists_frames_lift (productStructure A f) K e he χ q hq hn N φM
    (testCover (productStructure A f) K Ã).U (testCover (productStructure A f) K Ã).isAffineOpen
    (testCover_preimage_le (productStructure A f) K χ q hqρ)
  have hh' := pullbackCocycle_frameCocycle_eq (productStructure A f) K (g := g) (e := e)
    (hge := hge) (χ := χ) (q := q) (N := N) (φ := φM)
    (U := (testCover (productStructure A f) K Ã).U)
    (hle := testCover_preimage_le (productStructure A f) K χ q hqρ) (fr := fr) (hfr := hfr)
    (hcoord := hcoord) (hW := testCover_pair_le (productStructure A f) K χ q hqρ)
  have hcoc : CocycleGluing.IsCocycle (CocycleGluing.frameCocycle fr hfr) :=
    CocycleGluing.isCocycle_of_isTransition hfr (CocycleGluing.isTransition_frameCocycle hfr)
  obtain ⟨c, hc⟩ := exists_cObs (productStructure A f) K g χ q hqρ hq jM hjMr
    (CocycleGluing.frameCocycle fr hfr) hh'
  exact ⟨c, cObs_cocycle (productStructure A f) K g χ q hqρ hπ jQ hjQ hg hq jM hjMinj hjMr
    hjMsq (CocycleGluing.frameCocycle fr hfr) hh' hcoc c hc⟩

include he hge hq hjMsq in
/-- **A cocycle gives a lift.** If `d c + φ_* z = 0`, the restriction of the class of `L'`
along `χ` lifts along the square-zero extension `q`. -/
theorem exists_classLift_of_cocycle (c : cplx (productStructure A f) K A₀ 1 ⊗[A₀] M)
    (hcc : (dif (productStructure A f) K A₀ 1).rTensor M c +
        (phiQ χ q (toAlgHom_comp_eq χ q) hπ jQ (hjQ0_of jQ hjQ) jM hjMinj hjMr).lTensor
          (cplx (productStructure A f) K A₀ 2) (zObs (productStructure A f) K jQ hjQ g hg) =
        0) :
    ∃ η : Classes A (algebraOver f Ã), classesPullback A (algHomOver f q) η =
      classesPullback A (algHomOver f χ) (Quotient.mk _ L') := by
  obtain ⟨N, -, -, φ, -, -⟩ := exists_deformation (productStructure A f) K g χ q
    (toAlgHom_comp_eq χ q) jM hjMr hjMsq hπ jQ hjQ hg hq hjMinj c hcc e he hge
  let φL : (LineBundle.pullback (relMap (productStructure A f) χ)).obj
        (toRel A f A₀ (carrierBundle A L')) ≅
      (LineBundle.pullback (relMap (productStructure A f) q)).obj N :=
    ObjectProperty.isoMk _ φ
  let e₀ : (LineBundle.pullback (productMap A (algHomOver f q))).obj
        ((LineBundle.pullback (affineComparison A f Ã)).obj N) ≅
      carrierBundle A ((relativePullback A (algHomOver f χ)).obj L') :=
    ofRelPullbackIso A f q N ≪≫
      (LineBundle.pullback (affineComparison A f B)).mapIso φL.symm ≪≫
      (LineBundle.pullback (affineComparison A f B)).mapIso
        (toRelPullbackIso A f χ (carrierBundle A L')) ≪≫
      ofRelToRelIso A f B _
  exact exists_class_of_carrierIso A f q _ _ e₀

end Obstruction

end TwoAxisRigidifiedLineBundle

end Langlands.AlgebraicGeometry.Picard
