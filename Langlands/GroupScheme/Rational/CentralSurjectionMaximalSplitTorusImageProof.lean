import Langlands.GroupScheme.Rational.CentralSurjectionMaximalSplitTorusImageStatement
import Langlands.GroupScheme.CentralSurjectionImage.SurjectiveCharacterPoint
import Langlands.GroupScheme.CentralSurjectionImage.PreimageCommutative
import Langlands.GroupScheme.Rational.SplitTorusImage
import Langlands.GroupScheme.Rational.SplitTorusMonomorphism
import Langlands.GroupScheme.Rational.SplitTorusCharacterRestriction
import Langlands.GroupScheme.Rational.CharacterFpqcProof

/-! # Maximality of split-torus images under central fppf surjections: proof -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

namespace CentralSurjectionImage

set_option backward.isDefEq.respectTransparency false

variable {k : Type u} [Field k]

/-- The rational characters of the split torus `𝔾_m^I` are `ℤ^I`. -/
def splitCharEquiv (I : Type u) [Finite I] :
    rationalCharacters (splitTorus (Spec (CommRingCat.of k)) I) ≃+ (I → ℤ) :=
  (rationalCharacters.equivCharacterLattice (splitTorus.commGroupScheme _ I)).trans
    (splitTorus.characterLatticeEquiv k I)

/-- Restriction of characters along an isomorphism is bijective. -/
theorem characterRestrict_bijective_of_iso {S : Scheme.{u}} {A B : GroupScheme S} (e : A ≅ B) :
    Function.Bijective (characterRestrict e.hom) := by
  refine ⟨fun χ ψ h => ?_, fun χ => ⟨characterRestrict e.inv χ, ?_⟩⟩
  · have := congrArg (characterRestrict e.inv) h
    rwa [← AddMonoidHom.comp_apply, ← AddMonoidHom.comp_apply, ← characterRestrict_comp,
      e.inv_hom_id, characterRestrict_id] at this
  · rw [← AddMonoidHom.comp_apply, ← characterRestrict_comp, e.hom_inv_id, characterRestrict_id]
    rfl

/-- A monomorphism of split tori over a field inducing an injection on rational characters is
an isomorphism. -/
theorem isIso_of_characterRestrict_injective {A B : GroupScheme (Spec (CommRingCat.of k))}
    (hA : IsSplitTorus A) (hB : IsSplitTorus B) (f : A ⟶ B) [Mono f.hom.hom] [Mono f.hom.hom.left]
    (hf : Function.Injective (characterRestrict f)) : IsIso f := by
  classical
  obtain ⟨I, hI, ⟨eA⟩⟩ := hA
  obtain ⟨J, hJ, ⟨eB⟩⟩ := hB
  let f' := eA.inv ≫ f ≫ eB.hom
  have hbij : Function.Bijective (characterRestrict f') := by
    have h1 := characterRestrict_bijective_of_iso eA.symm
    have h2 := characterRestrict_bijective_of_iso eB
    have hsurj := IsSplitTorus.characterRestrict_surjective_of_mono ⟨I, hI, ⟨eA⟩⟩
      ⟨J, hJ, ⟨eB⟩⟩ f
    have hfb : Function.Bijective (characterRestrict f) := ⟨hf, hsurj⟩
    rw [characterRestrict_comp, characterRestrict_comp]
    exact (h1.comp hfb).comp h2
  let E : (J → ℤ) ≃+ (I → ℤ) :=
    ((splitCharEquiv J).symm.trans (AddEquiv.ofBijective (characterRestrict f') hbij)).trans
      (splitCharEquiv I)
  have : Fintype I := Fintype.ofFinite I
  have : Fintype J := Fintype.ofFinite J
  have hcard : Nat.card I = Nat.card J := by
    have h := (E.toIntLinearEquiv).finrank_eq
    rw [Module.finrank_fintype_fun_eq_card, Module.finrank_fintype_fun_eq_card] at h
    rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, h]
  have : Mono f'.hom.hom := by
    change Mono (eA.inv.hom.hom ≫ f.hom.hom ≫ eB.hom.hom.hom)
    infer_instance
  have := splitTorus.isIso_of_mono_of_card_eq I J f' hcard
  have hf' : f = eA.hom ≫ f' ≫ eB.inv := by simp [f']
  rw [hf']
  infer_instance

section Main

variable {G H : GroupScheme (Spec (CommRingCat.of k))} (q : G ⟶ H)
  {T T' T'' : CommGroupScheme (Spec (CommRingCat.of k))}
  (i : T.toGrp ⟶ G) (j : T'.toGrp ⟶ H) (p : T ⟶ T') (j' : T''.toGrp ⟶ H) (f : T'.toGrp ⟶ T''.toGrp)

/-- **The key step.** A character of the larger split torus `T''` that vanishes on the image
`T'` of the maximal split torus is zero. -/
theorem characterRestrict_eq_zero_imp (hG : IsConnectedReductive G)
    (hH : IsConnectedReductive H) [Flat q.hom.hom.left] [Surjective q.hom.hom.left]
    (hq : IsCentral (kernelι q)) (hi : IsMaximalSplitTorus i) (hj' : IsSplitSubtorus j')
    (hsq : CommGroupScheme.groupHom p ≫ j = i ≫ q) (hf : f ≫ j' = j)
    (α : rationalCharacters T''.toGrp) (hα : characterRestrict f α = 0) : α = 0 := by
  classical
  have : IsAffineHom G.X.hom := hG.isAffineHom
  have : IsAffineHom H.X.hom := hH.isAffineHom
  have : Smooth G.X.hom := hG.smooth
  have : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  have : IsAffine H.X.left := isAffine_of_isAffineHom H.X.hom
  have : IsClosedImmersion j'.hom.hom.left := hj'.2
  have : Mono j'.hom.hom := Over.mono_of_mono_left _
  -- the preimage of `T''`
  have hπ : fpqcP (preπ q j').hom.hom.left :=
    ⟨MorphismProperty.of_isPullback (P := @QuasiCompact) (preimage_isPullback_scheme q j')
      inferInstance, preπ_flat q j', preπ_surjective q j'⟩
  let M := preimageComm q j' hj'.1 hπ hq
  have : IsClosedImmersion (preι q j').hom.hom.left := preι_isClosedImmersion q j'
  have hMX : (preι q j').hom.hom.left ≫ G.X.hom = M.toGrp.X.hom := Over.w (preι q j').hom.hom
  have : IsAffineHom M.toGrp.X.hom := by rw [← hMX]; infer_instance
  have : LocallyOfFiniteType M.toGrp.X.hom := by rw [← hMX]; infer_instance
  -- the maximal split torus lies in the preimage
  let tM : T.toGrp ⟶ M.toGrp := pullback.lift i (CommGroupScheme.groupHom p ≫ f)
    (by rw [Category.assoc, hf, hsq])
  have htM : tM ≫ preι q j' = i := pullback.lift_fst _ _ _
  by_contra hne
  -- a cocharacter of the preimage detecting `α`
  let χ : rationalCharacters M.toGrp := characterRestrict (preπ q j') α
  have hαs := RelativeRoot.characterFpqc k T'' hj'.1
    (rationalCharacters.equivCharacterLattice T'' α) hne
  have : Surjective (CommGroupScheme.groupHom
    (rationalCharacters.equivCharacterLattice T'' α)).hom.hom.left := hαs.2.2
  have : Surjective (preπ q j').hom.hom.left := preπ_surjective q j'
  have hχ : Surjective χ.toMul.hom.hom.left := by
    change Surjective ((preπ q j').hom.hom.left ≫ (CommGroupScheme.groupHom
      (rationalCharacters.equivCharacterLattice T'' α)).hom.hom.left)
    infer_instance
  obtain ⟨cμ, hcμ⟩ := exists_gm_characterRestrict_ne_zero_of_surjective (Z := M) χ hχ
  -- the split torus generated by `T` and the cocharacter
  let D₀c : CommGroupScheme (Spec (CommRingCat.of k)) :=
    { toGrp := T.toGrp ⊗ (Gm (Spec (CommRingCat.of k))).toGrp
      comm := (inferInstance :
        IsCommMonObj (T.toGrp.X ⊗ (Gm (Spec (CommRingCat.of k))).toGrp.X)) }
  have hD₀ : IsSplitTorus D₀c.toGrp := IsSplitTorus.tensor hi.1.1 isSplitTorus_gm
  let ψ : D₀c.toGrp ⟶ M.toGrp := Grp.homMk ((tM.hom.hom ⊗ₘ cμ.hom.hom) ≫ μ[M.toGrp.X])
  let inl : T.toGrp ⟶ D₀c.toGrp :=
    Grp.homMk (lift (𝟙 _) (toUnit _ ≫ η[(Gm (Spec (CommRingCat.of k))).toGrp.X]))
  let inr : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ D₀c.toGrp :=
    Grp.homMk (lift (toUnit _ ≫ η[T.toGrp.X]) (𝟙 _))
  have hinl : inl ≫ ψ = tM := by
    apply Grp.hom_ext
    change lift (𝟙 _) (toUnit _ ≫ η) ≫ (tM.hom.hom ⊗ₘ cμ.hom.hom) ≫ μ[M.toGrp.X] = tM.hom.hom
    rw [lift_map_assoc, ← Hom.mul_def, Category.id_comp, Category.assoc, IsMonHom.one_hom,
      ← Hom.one_def, mul_one]
  have hinr : inr ≫ ψ = cμ := by
    apply Grp.hom_ext
    change lift (toUnit _ ≫ η) (𝟙 _) ≫ (tM.hom.hom ⊗ₘ cμ.hom.hom) ≫ μ[M.toGrp.X] = cμ.hom.hom
    rw [lift_map_assoc, ← Hom.mul_def, Category.id_comp, Category.assoc, IsMonHom.one_hom,
      ← Hom.one_def, one_mul]
  obtain ⟨D', πD, iD, hiD, hfac, -⟩ :=
    IsSplitTorus.exists_factor_isSplitSubtorus (D := D₀c) hD₀ (ψ ≫ preι q j')
  have hu : (inl ≫ πD) ≫ iD = i := by
    rw [Category.assoc, hfac, ← Category.assoc, hinl, htM]
  have := hi.2 D' iD hiD (inl ≫ πD) hu
  obtain ⟨ν, hν⟩ : ∃ ν : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ T.toGrp,
      ν ≫ i = cμ ≫ preι q j' := by
    refine ⟨(inr ≫ πD) ≫ inv (inl ≫ πD), ?_⟩
    rw [← hu, Category.assoc, IsIso.inv_hom_id_assoc, Category.assoc, hfac, ← Category.assoc, hinr]
  have hcμπ : cμ ≫ preπ q j' = ν ≫ CommGroupScheme.groupHom p ≫ f := by
    have hmono : Mono j' := by
      constructor
      intro Z a b hab
      apply Grp.hom_ext
      exact (cancel_mono j'.hom.hom).mp (congrArg (fun φ => φ.hom.hom) hab)
    apply (cancel_mono j').mp
    calc (cμ ≫ preπ q j') ≫ j' = cμ ≫ preι q j' ≫ q := by rw [Category.assoc, preι_comp]
      _ = ν ≫ i ≫ q := by rw [← Category.assoc, ← hν, Category.assoc]
      _ = ν ≫ CommGroupScheme.groupHom p ≫ j := by rw [hsq]
      _ = (ν ≫ CommGroupScheme.groupHom p ≫ f) ≫ j' := by
        rw [← hf]
        simp only [Category.assoc]
  apply hcμ
  have e : characterRestrict cμ χ = characterRestrict (cμ ≫ preπ q j') α := by
    rw [characterRestrict_comp]
    rfl
  rw [e, hcμπ, characterRestrict_comp, characterRestrict_comp]
  simp [hα]

end Main

end CentralSurjectionImage

open CentralSurjectionImage in
/-- **Borel–Tits 2.20(ii), forward image.** -/
theorem centralSurjectionMaximalSplitTorusImage :
    CentralSurjectionMaximalSplitTorusImageStatement.{u} := by
  intro k _ G H q hG hH hqf hqs hql hq T T' i j p hi hj hpf hps hpl hsq
  refine ⟨hj, fun T'' j' hj' f hf => ?_⟩
  have : IsClosedImmersion j.hom.hom.left := hj.2
  have : Mono (f.hom.hom.left ≫ j'.hom.hom.left) := by
    rw [← Over.comp_left, ← Grp.comp_hom_hom, hf]
    infer_instance
  have : Mono f.hom.hom.left := mono_of_mono _ j'.hom.hom.left
  have : Mono f.hom.hom := Over.mono_of_mono_left _
  apply isIso_of_characterRestrict_injective hj.1 hj'.1 f
  intro α β hαβ
  have h := characterRestrict_eq_zero_imp q i j p j' f hG hH hq hi hj' hsq hf (α - β)
    (by rw [map_sub, hαβ, sub_self])
  exact sub_eq_zero.mp h

end Langlands.GroupScheme
