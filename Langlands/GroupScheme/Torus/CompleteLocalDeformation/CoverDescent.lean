import Langlands.GroupScheme.Torus.CompleteLocalDeformation.HomRigidity
import Langlands.GroupScheme.Torus.SpecialFibreHomDescentAssembly
import Langlands.GroupScheme.Descent.FpqcHomDescent

/-! # Descent of homomorphisms along a finite étale local splitting cover

Let `A` be a noetherian local ring and `B` a finite étale local `A`-algebra over which the group
`H` becomes diagonalizable and the special fibre of `G` becomes diagonalizable. A homomorphism
`f_B : H_B ⟶ G_B` whose special fibre is the base change of a homomorphism `f₀ : H_k ⟶ G_k` of
special fibres descends to a homomorphism `f : H ⟶ G` with `f_B` as base change along
`Spec B → Spec A` and `f₀` as special fibre.

The descent uses `Descent.FpqcHomDescent`. Its compatibility condition on `Spec B ×_A Spec B` is
moved to `Spec (B ⊗[A] B)`. There both pullbacks of `f_B` agree modulo the maximal ideal of
`B`, so they are equal by the rigidity theorem `eq_of_baseChange_eq_of_finite`. -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped TensorProduct

namespace Langlands.GroupScheme.CompleteLocalDeformation

open Langlands.GroupScheme.Descent

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000

section PullHom

variable {S₀ T U V : Scheme.{u}}

/-- Homomorphisms into a base change are determined by their projection to the original
group. -/
theorem hom_ext_baseChange_fst {r : T ⟶ S₀} {G : GroupScheme S₀} {X : GroupScheme T}
    {a b : X ⟶ (GroupScheme.baseChange r).obj G}
    (h : a.hom.hom.left ≫ pullback.fst G.X.hom r = b.hom.hom.left ≫ pullback.fst G.X.hom r) :
    a = b := by
  apply Grp.hom_ext
  apply Over.OverMorphism.ext
  apply pullback.hom_ext h
  exact (Over.w a.hom.hom).trans (Over.w b.hom.hom).symm

/-- A base-changed homomorphism commutes with the projections to the original groups. -/
@[reassoc] theorem baseChange_map_left_fst (f : T ⟶ S₀) {G H : GroupScheme S₀} (a : G ⟶ H) :
    ((GroupScheme.baseChange f).map a).hom.hom.left ≫ pullback.fst H.X.hom f =
      pullback.fst G.X.hom f ≫ a.hom.hom.left :=
  pullback.lift_fst _ _ _

/-- The inverse comparison followed by the iterated projection lies over the base map. -/
@[reassoc] theorem pullbackComparison_inv_fst_snd (f : T ⟶ S₀) (q : U ⟶ T) (r : U ⟶ S₀)
    (h : q ≫ f = r) (G : GroupScheme S₀) :
    (pullbackComparison f q r h G).inv.hom.hom.left ≫
        pullback.fst ((GroupScheme.baseChange f).obj G).X.hom q ≫ pullback.snd G.X.hom f =
      pullback.snd G.X.hom r ≫ q := by
  have h1 : pullback.fst ((GroupScheme.baseChange f).obj G).X.hom q ≫
      pullback.snd G.X.hom f =
        pullback.snd ((GroupScheme.baseChange f).obj G).X.hom q ≫ q :=
    pullback.condition
  rw [h1, ← Category.assoc]
  congr 1
  exact Over.w (pullbackComparison f q r h G).inv.hom.hom

/-- The projection of a pulled-back homomorphism to the original target group. -/
theorem pullHom_left_fst (q : U ⟶ T) {f : T ⟶ S₀} {r : U ⟶ S₀} (hf : q ≫ f = r)
    {G H : GroupScheme S₀}
    (a : (GroupScheme.baseChange f).obj G ⟶ (GroupScheme.baseChange f).obj H) :
    (pullHom q hf hf a).hom.hom.left ≫ pullback.fst H.X.hom r =
      (pullbackComparison f q r hf G).inv.hom.hom.left ≫
        pullback.fst ((GroupScheme.baseChange f).obj G).X.hom q ≫
          a.hom.hom.left ≫ pullback.fst H.X.hom f := by
  simp only [pullHom, Grp.comp_hom_hom, Over.comp_left, Category.assoc,
    pullbackComparison_hom_fst, baseChange_map_left_fst_assoc]

/-- Pulling back twice is pulling back along the composite. -/
theorem pullHom_pullHom (q₁ : U ⟶ T) (q₂ : V ⟶ U) (q : V ⟶ T) (hq : q₂ ≫ q₁ = q)
    {f : T ⟶ S₀} {r₁ : U ⟶ S₀} {r₂ : V ⟶ S₀} (h₁ : q₁ ≫ f = r₁) (h₂ : q₂ ≫ r₁ = r₂)
    (h : q ≫ f = r₂) {G H : GroupScheme S₀}
    (a : (GroupScheme.baseChange f).obj G ⟶ (GroupScheme.baseChange f).obj H) :
    pullHom q₂ h₂ h₂ (pullHom q₁ h₁ h₁ a) = pullHom q h h a := by
  apply hom_ext_baseChange_fst
  rw [pullHom_left_fst, pullHom_left_fst, pullHom_left_fst]
  have key : (pullbackComparison r₁ q₂ r₂ h₂ G).inv.hom.hom.left ≫
      pullback.fst ((GroupScheme.baseChange r₁).obj G).X.hom q₂ ≫
        (pullbackComparison f q₁ r₁ h₁ G).inv.hom.hom.left ≫
          pullback.fst ((GroupScheme.baseChange f).obj G).X.hom q₁ =
      (pullbackComparison f q r₂ h G).inv.hom.hom.left ≫
        pullback.fst ((GroupScheme.baseChange f).obj G).X.hom q := by
    apply pullback.hom_ext
    · simp only [Category.assoc, pullbackComparison_inv_fst]
    · simp only [Category.assoc, pullbackComparison_inv_fst_snd,
        pullbackComparison_inv_fst_snd_assoc, hq]
  have key' := key =≫ (a.hom.hom.left ≫ pullback.fst H.X.hom f)
  simpa only [Category.assoc] using key'

/-- Equal pullbacks give equal base changes. -/
theorem baseChange_map_eq_of_pullHom_eq (q : U ⟶ T) {f : T ⟶ S₀} {r : U ⟶ S₀}
    (hf : q ≫ f = r) {G H : GroupScheme S₀}
    {a b : (GroupScheme.baseChange f).obj G ⟶ (GroupScheme.baseChange f).obj H}
    (h : pullHom q hf hf a = pullHom q hf hf b) :
    (GroupScheme.baseChange q).map a = (GroupScheme.baseChange q).map b := by
  have h' := congrArg (fun x => (pullbackComparison f q r hf G).hom ≫ x ≫
    (pullbackComparison f q r hf H).inv) h
  simpa [pullHom] using h'

/-- Agreement of the two pullbacks to the overlap gives compatibility with the canonical
descent data. -/
theorem compatible_of_pullHom_eq {S B₀ : Scheme.{u}} (p : S ⟶ B₀) {C D : GroupScheme B₀}
    (f : (GroupScheme.baseChange p).obj C ⟶ (GroupScheme.baseChange p).obj D)
    (h : pullHom (fst p) (rfl : fst p ≫ p = fst p ≫ p) rfl f =
      pullHom (snd p) pullback.condition.symm pullback.condition.symm f) :
    Compatible (canonicalDatum p C) (canonicalDatum p D) f := by
  change (GroupScheme.baseChange (fst p)).map f ≫
      ((pullbackComparison p (fst p) (fst p ≫ p) rfl D).hom ≫
        (pullbackComparison p (snd p) (fst p ≫ p) pullback.condition.symm D).inv) =
    ((pullbackComparison p (fst p) (fst p ≫ p) rfl C).hom ≫
        (pullbackComparison p (snd p) (fst p ≫ p) pullback.condition.symm C).inv) ≫
      (GroupScheme.baseChange (snd p)).map f
  simp only [pullHom] at h
  have h' : (GroupScheme.baseChange (fst p)).map f ≫
      (pullbackComparison p (fst p) (fst p ≫ p) rfl D).hom =
    (pullbackComparison p (fst p) (fst p ≫ p) rfl C).hom ≫
      (pullbackComparison p (snd p) (fst p ≫ p) pullback.condition.symm C).inv ≫
        (GroupScheme.baseChange (snd p)).map f ≫
          (pullbackComparison p (snd p) (fst p ≫ p) pullback.condition.symm D).hom := by
    rw [← h]
    simp
  rw [← Category.assoc, h']
  simp

/-- Base change along an fpqc morphism is faithful on homomorphisms. -/
theorem baseChange_map_injective {S B₀ : Scheme.{u}} (p : S ⟶ B₀) [Flat p] [Surjective p]
    [QuasiCompact p] {C D : GroupScheme B₀} {a b : C ⟶ D}
    (h : (GroupScheme.baseChange p).map a = (GroupScheme.baseChange p).map b) : a = b := by
  have hf := canonicalDatum_compatible p a
  rw [FpqcHomDescent.unique p _ hf a rfl, FpqcHomDescent.unique p _ hf b h.symm]

end PullHom

section Cover

open IsLocalRing

/-- The special-fibre comparison of a local base change, written with the comparison
isomorphisms of `Descent.Data`. -/
theorem specialFibreBaseChangeIso_eq {A B : Type u} [CommRing A] [IsLocalRing A]
    [CommRing B] [IsLocalRing B] [Algebra A B] [IsLocalHom (algebraMap A B)]
    (G : GroupScheme (Spec (CommRingCat.of A)))
    (hc : Spec.algebraMap B (ResidueField B) ≫ Spec.algebraMap A B =
      Spec.algebraMap (ResidueField A) (ResidueField B) ≫
        Spec.algebraMap A (ResidueField A)) :
    specialFibreBaseChangeIso G =
      pullbackComparison (Spec.algebraMap A B) (Spec.algebraMap B (ResidueField B)) _ hc G ≪≫
        (pullbackComparison (Spec.algebraMap A (ResidueField A))
          (Spec.algebraMap (ResidueField A) (ResidueField B)) _ rfl G).symm := by
  apply Iso.ext
  unfold Descent.pullbackComparison
  simp [specialFibreBaseChangeIso]

variable {A : Type u} [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
  {G H : GroupScheme (Spec (CommRingCat.of A))}

/-- **Descent along a finite étale local splitting cover.** Let `B` be the carrier of a local
splitting cover of `H` over which the special fibre of `G` is diagonalizable. A homomorphism
`f_B : H_B ⟶ G_B` whose special fibre is the base change of `f₀ : H_k ⟶ G_k` (through the
canonical special-fibre comparison) descends to a homomorphism `f : H ⟶ G` with base change
`f_B` and special fibre `f₀`. -/
theorem exists_descent_of_specialFibre [IsAffineHom G.X.hom] (d : LocalSplittingData A H)
    (hG : RelativeMultiplicativeType.IsDiagonalizable
      ((GroupScheme.baseChange (Spec.algebraMap d.Carrier (ResidueField d.Carrier))).obj
        ((GroupScheme.baseChange (Spec.algebraMap A d.Carrier)).obj G)))
    (f₀ : (GroupScheme.baseChange (Spec.algebraMap A (ResidueField A))).obj H ⟶
      (GroupScheme.baseChange (Spec.algebraMap A (ResidueField A))).obj G)
    (fB : (GroupScheme.baseChange (Spec.algebraMap A d.Carrier)).obj H ⟶
      (GroupScheme.baseChange (Spec.algebraMap A d.Carrier)).obj G)
    (hfB : (GroupScheme.baseChange
        (Spec.algebraMap d.Carrier (ResidueField d.Carrier))).map fB ≫
          (specialFibreBaseChangeIso G).hom =
      (specialFibreBaseChangeIso H).hom ≫
        (GroupScheme.baseChange
          (Spec.algebraMap (ResidueField A) (ResidueField d.Carrier))).map f₀) :
    ∃ f : H ⟶ G, (GroupScheme.baseChange (Spec.algebraMap A d.Carrier)).map f = fB ∧
      (GroupScheme.baseChange (Spec.algebraMap A (ResidueField A))).map f = f₀ := by
  classical
  let B := d.Carrier
  let p := Spec.algebraMap A B
  let spA := Spec.algebraMap A (ResidueField A)
  let spB := Spec.algebraMap B (ResidueField B)
  let jk := Spec.algebraMap (ResidueField A) (ResidueField B)
  have hc : spB ≫ p = jk ≫ spA := by
    simp only [spB, p, jk, spA, Spec.algebraMap, ← Spec.map_comp]
    congr 1
  -- The special-fibre hypothesis as an equality of pulled-back homomorphisms.
  have hcomp : pullHom spB hc hc fB = pullHom jk rfl rfl f₀ := by
    rw [specialFibreBaseChangeIso_eq G hc, specialFibreBaseChangeIso_eq H hc] at hfB
    simp only [Iso.trans_hom, Iso.symm_hom] at hfB
    have h' := congrArg (fun x =>
      (pullbackComparison p spB (jk ≫ spA) hc H).inv ≫ x ≫
        (pullbackComparison spA jk (jk ≫ spA) rfl G).hom) hfB
    simpa [pullHom] using h'
  -- The tensor square of `B` and its two maps to `B`.
  let R := B ⊗[A] B
  let iL : Spec (CommRingCat.of R) ⟶ Spec (CommRingCat.of B) := Spec.algebraMap B R
  let iR : Spec (CommRingCat.of R) ⟶ Spec (CommRingCat.of B) :=
    Spec.map (CommRingCat.ofHom
      (Algebra.TensorProduct.includeRight : B →ₐ[A] R).toRingHom)
  have hring : ∀ a : A, algebraMap B R (algebraMap A B a) =
      (Algebra.TensorProduct.includeRight : B →ₐ[A] R) (algebraMap A B a) := by
    intro a
    rw [AlgHom.commutes, ← IsScalarTower.algebraMap_apply]
  have hR : iR ≫ p = iL ≫ p := by
    simp only [iR, iL, p, Spec.algebraMap, ← Spec.map_comp]
    congr 1
    ext a
    exact (hring a).symm
  let e : Overlap p ⟶ Spec (CommRingCat.of R) := (pullbackSpecIso A B B).hom
  have heL : e ≫ iL = fst p := pullbackSpecIso_hom_fst' A B B
  have heR : e ≫ iR = snd p := pullbackSpecIso_hom_snd A B B
  -- The reduction of the tensor square modulo the maximal ideal of `B`.
  let I : Ideal R := (maximalIdeal B).map (algebraMap B R)
  let π : Spec (CommRingCat.of (R ⧸ I)) ⟶ Spec (CommRingCat.of R) := Spec.algebraMap R (R ⧸ I)
  have hmB : (maximalIdeal A).map (algebraMap A B) = maximalIdeal B :=
    d.residueData.map_maximalIdeal
  have hRle : maximalIdeal B ≤
      I.comap (Algebra.TensorProduct.includeRight : B →ₐ[A] R).toRingHom := by
    rw [← Ideal.map_le_iff_le_comap, ← hmB, Ideal.map_map]
    have hcomp' : (Algebra.TensorProduct.includeRight : B →ₐ[A] R).toRingHom.comp
        (algebraMap A B) = (algebraMap B R).comp (algebraMap A B) := by
      ext a
      exact (hring a).symm
    rw [hcomp', ← Ideal.map_map, hmB]
  let k₁ : ResidueField B →+* R ⧸ I := Ideal.quotientMap I (algebraMap B R) Ideal.le_comap_map
  let k₂ : ResidueField B →+* R ⧸ I :=
    Ideal.quotientMap I (Algebra.TensorProduct.includeRight : B →ₐ[A] R).toRingHom hRle
  let κ₁ : Spec (CommRingCat.of (R ⧸ I)) ⟶ Spec (CommRingCat.of (ResidueField B)) :=
    Spec.map (CommRingCat.ofHom k₁)
  let κ₂ : Spec (CommRingCat.of (R ⧸ I)) ⟶ Spec (CommRingCat.of (ResidueField B)) :=
    Spec.map (CommRingCat.ofHom k₂)
  have E₁ : κ₁ ≫ spB = π ≫ iL := by
    simp only [κ₁, spB, π, iL, Spec.algebraMap, ← Spec.map_comp]
    congr 1
  have E₂ : κ₂ ≫ spB = π ≫ iR := by
    simp only [κ₂, spB, π, iR, Spec.algebraMap, ← Spec.map_comp]
    congr 1
  have E₃ : κ₂ ≫ jk = κ₁ ≫ jk := by
    simp only [κ₁, κ₂, jk, Spec.algebraMap, ← Spec.map_comp]
    congr 1
    apply CommRingCat.hom_ext
    apply Ideal.Quotient.ringHom_ext
    ext a
    change Ideal.Quotient.mk I
        ((Algebra.TensorProduct.includeRight : B →ₐ[A] R) (algebraMap A B a)) =
      Ideal.Quotient.mk I (algebraMap B R (algebraMap A B a))
    rw [hring a]
  -- The groups over the tensor square.
  have : IsAffine ((GroupScheme.baseChange (iL ≫ p)).obj G).X.left := by
    change IsAffine (pullback G.X.hom (iL ≫ p))
    infer_instance
  have hH' : RelativeMultiplicativeType.IsDiagonalizable
      ((GroupScheme.baseChange (iL ≫ p)).obj H) :=
    RelativeMultiplicativeType.IsDiagonalizable.of_iso
      (pullbackComparison p iL (iL ≫ p) rfl H).symm (d.split.baseChange iL)
  have h₁ : (κ₁ ≫ spB) ≫ p = π ≫ iL ≫ p := by
    rw [E₁, Category.assoc]
  have hG' : RelativeMultiplicativeType.IsDiagonalizable
      ((GroupScheme.baseChange π).obj ((GroupScheme.baseChange (iL ≫ p)).obj G)) :=
    RelativeMultiplicativeType.IsDiagonalizable.of_iso
      (pullbackComparison (iL ≫ p) π (π ≫ iL ≫ p) rfl G ≪≫
        (pullbackComparison p (κ₁ ≫ spB) (π ≫ iL ≫ p) h₁ G).symm ≪≫
          (pullbackComparison spB κ₁ (κ₁ ≫ spB) rfl
            ((GroupScheme.baseChange p).obj G)).symm)
      (hG.baseChange κ₁)
  -- Both pullbacks of `fB` to the tensor square agree.
  have hρ₁ : κ₁ ≫ jk ≫ spA = π ≫ iL ≫ p := by
    rw [← hc, ← Category.assoc, E₁, Category.assoc]
  have hρ₂ : κ₂ ≫ jk ≫ spA = π ≫ iL ≫ p := by
    rw [← hc, ← Category.assoc, E₂, Category.assoc, hR]
  have hw : pullHom iL rfl rfl fB = pullHom iR hR hR fB := by
    apply eq_of_baseChange_eq_of_finite (A := B) hH' hG'
    apply baseChange_map_eq_of_pullHom_eq π (rfl : π ≫ iL ≫ p = π ≫ iL ≫ p)
    rw [pullHom_pullHom iL π (π ≫ iL) rfl rfl rfl (Category.assoc _ _ _) fB,
      pullHom_pullHom iR π (π ≫ iR) rfl hR rfl (by rw [Category.assoc, hR]) fB,
      ← pullHom_pullHom spB κ₁ (π ≫ iL) E₁ hc hρ₁ (Category.assoc _ _ _) fB,
      ← pullHom_pullHom spB κ₂ (π ≫ iR) E₂ hc hρ₂ (by rw [Category.assoc, hR]) fB,
      hcomp,
      pullHom_pullHom jk κ₁ (κ₁ ≫ jk) rfl rfl hρ₁ (by rw [Category.assoc, hρ₁]) f₀,
      pullHom_pullHom jk κ₂ (κ₁ ≫ jk) E₃ rfl hρ₂ (by rw [Category.assoc, hρ₁]) f₀]
  -- Compatibility with the canonical descent data, and descent.
  have he₁ : e ≫ iL ≫ p = fst p ≫ p := by
    rw [← Category.assoc, heL]
  have hcompat : Compatible (canonicalDatum p H) (canonicalDatum p G) fB := by
    apply compatible_of_pullHom_eq
    rw [← pullHom_pullHom iL e (fst p) heL rfl he₁ rfl fB,
      ← pullHom_pullHom iR e (snd p) heR hR he₁ pullback.condition.symm fB, hw]
  have : Flat p := HasRingHomProperty.Spec_iff.mpr (RingHom.flat_algebraMap_iff.mpr inferInstance)
  have : Flat jk :=
    HasRingHomProperty.Spec_iff.mpr (RingHom.flat_algebraMap_iff.mpr
      (inferInstance : Module.Flat (ResidueField A) (ResidueField B)))
  have : Surjective jk :=
    ((flat_and_surjective_SpecMap_iff _).mpr
      (RingHom.faithfullyFlat_algebraMap_iff.mpr
        (inferInstance : Module.FaithfullyFlat (ResidueField A) (ResidueField B)))).2
  have hFB : (GroupScheme.baseChange p).map (FpqcHomDescent.hom p fB hcompat) = fB :=
    FpqcHomDescent.baseChange_hom p fB hcompat
  refine ⟨FpqcHomDescent.hom p fB hcompat, hFB, ?_⟩
  apply baseChange_map_injective jk
  apply baseChange_map_eq_of_pullHom_eq jk (rfl : jk ≫ spA = jk ≫ spA)
  have h1 := pullHom_map spB p (jk ≫ spA) hc (FpqcHomDescent.hom p fB hcompat)
  rw [hFB, hcomp] at h1
  rw [h1, pullHom_map]

/-- The same descent, with the special-fibre hypothesis in the form
`(baseChange spB).map fB = specialHomTransport f₀` used by
`specialFibre_hom_bijective_of_cover`. -/
theorem exists_descent_of_specialHomTransport [IsAffineHom G.X.hom]
    (d : LocalSplittingData A H)
    (hG : RelativeMultiplicativeType.IsDiagonalizable
      ((GroupScheme.baseChange (Spec.algebraMap d.Carrier (ResidueField d.Carrier))).obj
        ((GroupScheme.baseChange (Spec.algebraMap A d.Carrier)).obj G)))
    (f₀ : (GroupScheme.baseChange (Spec.algebraMap A (ResidueField A))).obj H ⟶
      (GroupScheme.baseChange (Spec.algebraMap A (ResidueField A))).obj G)
    (fB : (GroupScheme.baseChange (Spec.algebraMap A d.Carrier)).obj H ⟶
      (GroupScheme.baseChange (Spec.algebraMap A d.Carrier)).obj G)
    (hfB : (GroupScheme.baseChange
        (Spec.algebraMap d.Carrier (ResidueField d.Carrier))).map fB =
      specialHomTransport (B := d.Carrier) f₀) :
    ∃ f : H ⟶ G, (GroupScheme.baseChange (Spec.algebraMap A d.Carrier)).map f = fB ∧
      (GroupScheme.baseChange (Spec.algebraMap A (ResidueField A))).map f = f₀ :=
  exists_descent_of_specialFibre d hG f₀ fB ((specialHomTransport_eq_iff f₀ fB).mp hfB)

/-- The structure map of a local splitting cover is flat. -/
instance LocalSplittingData.specFlat (d : LocalSplittingData A H) :
    Flat (Spec.algebraMap A d.Carrier) :=
  HasRingHomProperty.Spec_iff.mpr (RingHom.flat_algebraMap_iff.mpr inferInstance)

end Cover

end Langlands.GroupScheme.CompleteLocalDeformation
