import Langlands.AlgebraicGeometry.AffineCechDeRhamLocalMorphisms
import Langlands.AlgebraicGeometry.Modules.FormalModuleSystemPresheaves
import Langlands.AlgebraicGeometry.SmoothThickeningLiftingProof

/-!
# Degree-one Čech–de Rham pullback of a morphism on a square-zero reduction

For a square-zero ideal `I` of `R` and a morphism over `Spec R` from the base
change of `X` to `Spec (R ⧸ I)` into `Y`, smoothness of `Y` gives lifts on the
affine charts of `X`. The section pullbacks of these lifts define the corrected
degree-one pullback of Kai-Wen Lan, *Arithmetic compactifications of PEL-type
Shimura varieties*, revised 14 March 2021, Proposition 2.1.6.4, printed
pp. 133–135, on the affine Čech–de Rham modules of fixed compatible covers.
-/

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace AlgebraicGeometry
open Langlands.AlgebraicGeometry.Modules.FormalModuleSystemPresheaves

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.AlgebraicGeometry.AffineCechDeRham

variable {R : Type u} [CommRing R] {X Y : Scheme.{u}}
  (f : X ⟶ Spec (CommRingCat.of R)) {g : Y ⟶ Spec (CommRingCat.of R)} (I : Ideal R)

/-- The base immersion from the quotient ring. -/
abbrev quotientBaseMap := Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))

/-- The actual scheme obtained by base change to the quotient ring. -/
abbrev quotientReduction := pullback f (quotientBaseMap I)

/-- The projection from the actual reduction to the thicker scheme. -/
abbrev quotientReductionMap : quotientReduction f I ⟶ X := pullback.fst f (quotientBaseMap I)

instance quotientBaseMap_isClosedImmersion : IsClosedImmersion (quotientBaseMap I) :=
  IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective

instance quotientReductionMap_isClosedImmersion : IsClosedImmersion (quotientReductionMap f I) := by
  unfold quotientReductionMap
  infer_instance

/-- A square-zero base reduction is surjective on points. -/
lemma quotientReductionMap_surjective (hI : I * I = ⊥) : Surjective (quotientReductionMap f I) := by
  have hrad : I ≤ nilradical R := by
    intro a ha
    refine ⟨2, ?_⟩
    have haa := Ideal.mul_mem_mul ha ha
    rwa [hI, Ideal.mem_bot, ← pow_two] at haa
  have hq : Surjective (quotientBaseMap I) :=
    ⟨(PrimeSpectrum.comap_quotientMk_bijective_of_le_nilradical hrad).2⟩
  exact MorphismProperty.of_isPullback (P := @Surjective)
    (IsPullback.of_hasPullback f (quotientBaseMap I)).flip hq

/-- Reduction on an affine section ring is surjective with kernel the extension
of the base ideal. -/
lemma quotientReductionMap_appLE (W : X.Opens) (hW : IsAffineOpen W) :
    let r := quotientReductionMap f I
    Function.Surjective (r.appLE W (r ⁻¹ᵁ W) le_rfl).hom ∧
      RingHom.ker (r.appLE W (r ⁻¹ᵁ W) le_rfl).hom =
        I.map (algebraMap R ((sectionAlgebras f).obj (op W))) := by
  let r := quotientReductionMap f I
  have hs := surjective_and_ker_app f (𝟙 X) r (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective
    f (pullback.snd f (quotientBaseMap I)) (IsPullback.of_hasPullback f (quotientBaseMap I))
    (by simp) I (by rw [Ideal.mk_ker, Algebra.algebraMap_self, Ideal.map_id]) ⟨W, hW⟩
  change Function.Surjective (r.appLE W (r ⁻¹ᵁ W) le_rfl).hom ∧
    RingHom.ker (r.appLE W (r ⁻¹ᵁ W) le_rfl).hom =
      I.map (Scheme.TwoAffineOpenCover.algebraOfHom f W).algebraMap
  rw [Scheme.Hom.appLE_eq_app]
  exact hs

section Lifts

variable [Smooth g] (hI : I * I = ⊥) (m : quotientReduction f I ⟶ Y)
  (hm : m ≫ g = quotientReductionMap f I ≫ f)

include hI hm in
/-- A map on the reduction lifts over each thicker affine open. -/
theorem exists_lift_on_affineOpen (W : X.Opens) (hW : IsAffineOpen W) :
    let r := quotientReductionMap f I
    ∃ ℓ : W.toScheme ⟶ Y, ℓ ≫ g = W.ι ≫ f ∧
      r.resLE W (r ⁻¹ᵁ W) le_rfl ≫ ℓ = (r ⁻¹ᵁ W).ι ≫ m := by
  let r := quotientReductionMap f I
  let W₀ := r ⁻¹ᵁ W
  let s := r.resLE W W₀ le_rfl
  let : IsAffine W.toScheme := hW
  let : IsAffine W₀.toScheme := hW.preimage r
  let q := s.appTop
  have hq : q = W.topIso.hom ≫ r.appLE W W₀ le_rfl ≫ W₀.topIso.inv := by
    have h := (arrowResLEAppIso r W W₀ le_rfl).hom.w.symm
    change q ≫ W₀.topIso.hom = W.topIso.hom ≫ r.appLE W W₀ le_rfl at h
    calc
      q = (q ≫ W₀.topIso.hom) ≫ W₀.topIso.inv := by
        rw [Category.assoc, Iso.hom_inv_id, Category.comp_id]
      _ = _ := by rw [h, Category.assoc]
  obtain ⟨hsurj, hker⟩ := quotientReductionMap_appLE f I W hW
  have hsurj_q : Function.Surjective q.hom := by
    rw [hq, surjective_comp_iff_of_isIso_left, surjective_comp_iff_of_isIso_right]
    exact hsurj
  have hnil_q : IsNilpotent (RingHom.ker q.hom) := by
    let A := (sectionAlgebras f).obj (op W)
    have hSq : (I.map (algebraMap R A)) ^ 2 = ⊥ := by
      rw [pow_two, ← Ideal.map_mul, hI, Ideal.map_bot]
    refine ⟨2, ?_⟩
    rw [hq, ker_comp_eq_comap, ker_comp_of_injective _ _ (inj_hom_of_isIso _),
      hker, comap_hom_eq_map_inv]
    change ((I.map (algebraMap R A)).map W.topIso.inv.hom) ^ 2 = ⊥
    rw [← Ideal.map_pow, hSq, Ideal.map_bot]
  let x₀ := W₀.toScheme.isoSpec.inv ≫ W₀.ι ≫ m
  let p := W.toScheme.isoSpec.inv ≫ W.ι ≫ f
  have hbase : x₀ ≫ g = Spec.map q ≫ p := by
    dsimp only [x₀, p]
    rw [Category.assoc, Category.assoc, hm, Scheme.isoSpec_inv_naturality_assoc s,
      Scheme.Hom.resLE_comp_ι_assoc]
  obtain ⟨x, hx, hxbase⟩ := smoothThickeningLifting g q hsurj_q hnil_q x₀ p hbase
  refine ⟨W.toScheme.isoSpec.hom ≫ x, ?_, ?_⟩
  · simp [Category.assoc, hxbase, p]
  · rw [← Category.assoc, ← Scheme.isoSpec_hom_naturality, Category.assoc, hx]
    simp [x₀, W₀, r]

variable {U : Scheme.AffineOpenCover.{u} X} {V : Scheme.AffineOpenCover.{u} Y}
  (β : U.I₀ → V.I₀)
  (hβ : ∀ i, quotientReductionMap f I ⁻¹ᵁ coverOpens U i ≤ m ⁻¹ᵁ coverOpens V (β i))
  [IsSeparated f]

private def chosenAffineLift (i : U.I₀) :
    let W := coverOpens U i
    let r := quotientReductionMap f I
    { ℓ : W.toScheme ⟶ Y // ℓ ≫ g = W.ι ≫ f ∧
      r.resLE W (r ⁻¹ᵁ W) le_rfl ≫ ℓ = (r ⁻¹ᵁ W).ι ≫ m } :=
  Classical.indefiniteDescription _ (exists_lift_on_affineOpen f I hI m hm (coverOpens U i)
    (AlgebraicGeometry.isAffineOpen_opensRange (U.f i)))

/-- A morphism on the quotient reduction yields a system of affine pullbacks
for every pair of covers compatible with the reduced morphism. -/
def localPullbacksOfReduction : LocalPullbacks (f := f) (g := g) I β :=
  letI := quotientReductionMap_surjective f I hI
  LocalPullbacks.ofLocalMorphisms (quotientReductionMap f I) m β
    (fun i => (chosenAffineLift f I hI m hm i).val)
    (fun i => (chosenAffineLift f I hI m hm i).property.1)
    (fun i => (chosenAffineLift f I hI m hm i).property.2) hβ I
    (fun W hW => (quotientReductionMap_appLE f I W hW).2)

variable [Smooth f] [Finite U.I₀] [IsSeparated g] [Finite V.I₀]

/-- The corrected pullback in degree one for a morphism defined on the actual
square-zero base reduction. -/
def reductionPullbackH1 : H1 g V →ₗ[R] H1 f U :=
  (localPullbacksOfReduction f I hI m hm β hβ).pullbackH1 hI

/-- The degree-one comparison is independent of the affine lifts for the
fixed compatible covers. -/
theorem reductionPullbackH1_eq_of_localMorphisms
    (ℓ : ∀ i, (coverOpens U i).toScheme ⟶ Y)
    (hℓ : ∀ i, ℓ i ≫ g = (coverOpens U i).ι ≫ f)
    (hred : ∀ i, (quotientReductionMap f I).resLE (coverOpens U i)
      (quotientReductionMap f I ⁻¹ᵁ coverOpens U i) le_rfl ≫ ℓ i =
        (quotientReductionMap f I ⁻¹ᵁ coverOpens U i).ι ≫ m) :
    letI := quotientReductionMap_surjective f I hI
    reductionPullbackH1 f I hI m hm β hβ =
      (LocalPullbacks.ofLocalMorphisms (quotientReductionMap f I) m β ℓ hℓ hred hβ I
        (fun W hW => (quotientReductionMap_appLE f I W hW).2)).pullbackH1 hI := by
  let : Surjective (quotientReductionMap f I) := quotientReductionMap_surjective f I hI
  dsimp only [reductionPullbackH1]
  apply LocalPullbacks.pullbackH1_eq_of_congruent
  intro p τ i j a
  exact localMorphisms_congruent (quotientReductionMap f I) m β
    (fun k => (chosenAffineLift f I hI m hm k).val)
    (fun k => (chosenAffineLift f I hI m hm k).property.1)
    (fun k => (chosenAffineLift f I hI m hm k).property.2) hβ I
    (fun W hW => (quotientReductionMap_appLE f I W hW).2) ℓ hℓ hred τ i j a

/-- Any two families of local lifts of the reduced morphism on the charts of
the fixed compatible covers induce the same degree-one map. -/
theorem pullbackH1_ofLocalMorphisms_eq
    (ℓ ℓ' : ∀ i, (coverOpens U i).toScheme ⟶ Y)
    (hℓ : ∀ i, ℓ i ≫ g = (coverOpens U i).ι ≫ f)
    (hℓ' : ∀ i, ℓ' i ≫ g = (coverOpens U i).ι ≫ f)
    (hred : ∀ i, (quotientReductionMap f I).resLE (coverOpens U i)
      (quotientReductionMap f I ⁻¹ᵁ coverOpens U i) le_rfl ≫ ℓ i =
        (quotientReductionMap f I ⁻¹ᵁ coverOpens U i).ι ≫ m)
    (hred' : ∀ i, (quotientReductionMap f I).resLE (coverOpens U i)
      (quotientReductionMap f I ⁻¹ᵁ coverOpens U i) le_rfl ≫ ℓ' i =
        (quotientReductionMap f I ⁻¹ᵁ coverOpens U i).ι ≫ m) :
    letI := quotientReductionMap_surjective f I hI
    (LocalPullbacks.ofLocalMorphisms (quotientReductionMap f I) m β ℓ hℓ hred hβ I
        (fun W hW => (quotientReductionMap_appLE f I W hW).2)).pullbackH1 hI =
      (LocalPullbacks.ofLocalMorphisms (quotientReductionMap f I) m β ℓ' hℓ' hred' hβ I
        (fun W hW => (quotientReductionMap_appLE f I W hW).2)).pullbackH1 hI := by
  let : Surjective (quotientReductionMap f I) := quotientReductionMap_surjective f I hI
  apply LocalPullbacks.pullbackH1_eq_of_congruent
  intro p τ i j a
  exact localMorphisms_congruent (quotientReductionMap f I) m β ℓ hℓ hred hβ I
    (fun W hW => (quotientReductionMap_appLE f I W hW).2) ℓ' hℓ' hred' τ i j a

/-- If the reduced morphism lifts globally, its corrected pullback preserves
the first Hodge step of the thicker schemes. -/
theorem reductionPullbackH1_maps_hodgeF1_of_lift
    (γ : X ⟶ Y) (hγ : γ ≫ g = f) (hγ₀ : quotientReductionMap f I ≫ γ = m)
    {z : H1 g V} (hz : z ∈ hodgeF1 g V) :
    reductionPullbackH1 f I hI m hm β hβ z ∈ hodgeF1 f U := by
  let r := quotientReductionMap f I
  let : Surjective r := quotientReductionMap_surjective f I hI
  have hγβ (i : U.I₀) : coverOpens U i ≤ γ ⁻¹ᵁ coverOpens V (β i) := by
    intro x hx
    obtain ⟨y, rfl⟩ := r.surjective x
    change γ (r y) ∈ coverOpens V (β i)
    rw [← Scheme.Hom.comp_apply, hγ₀]
    exact hβ i hx
  let L := localPullbacksOfReduction f I hI m hm β hβ
  let G := LocalPullbacks.ofMorphism I γ hγ β hγβ
  have heq : L.pullbackH1 hI = G.pullbackH1 hI :=
    L.pullbackH1_eq_of_congruent hI G (fun τ i j a =>
      localMorphisms_congruent_global r m β
        (fun k => (chosenAffineLift f I hI m hm k).val)
        (fun k => (chosenAffineLift f I hI m hm k).property.1)
        (fun k => (chosenAffineLift f I hI m hm k).property.2) hβ I
        (fun W hW => (quotientReductionMap_appLE f I W hW).2) γ hγ hγ₀ hγβ τ i j a)
  change L.pullbackH1 hI z ∈ hodgeF1 f U
  rw [heq]
  exact G.pullbackH1_maps_hodgeF1 hI (fun _ => rfl) hz

end Lifts

end Langlands.AlgebraicGeometry.AffineCechDeRham
