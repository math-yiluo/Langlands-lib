import Langlands.GroupScheme.Torus.GaloisInvariantLatticesStatement
import Langlands.GroupScheme.Descent.GaloisHom

/-! # Galois descent of characters and cocharacters -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- Coherence of the canonical `𝔾ₘ` comparisons with descent transport, obtained from the
identity character of `𝔾ₘ` and `rationalCharacters.transportCharacter_baseChange`. -/
private theorem gm_descent_comparison {B S : Scheme.{u}} (b : S ⟶ B) (a : S ⟶ S)
    (ha : a ≫ b = b) :
    (GroupScheme.baseChange a).map (Gm.baseChangeIso b).hom ≫ (Gm.baseChangeIso a).hom =
      (descentBaseChangeIso b a ha (Gm B).toGrp).hom ≫ (Gm.baseChangeIso b).hom := by
  let c : rationalCharacters (Gm B).toGrp := Additive.ofMul (𝟙 _)
  have h :
      transportCharacter b a ha (Gm B).toGrp (Gm.baseChangeIso b).hom =
        (Gm.baseChangeIso b).hom := by
    have h := rationalCharacters.transportCharacter_baseChange b a ha c
    rw [rationalCharacters.baseChange_toMul] at h
    change transportCharacter b a ha (Gm B).toGrp
        ((GroupScheme.baseChange b).map (𝟙 _) ≫ (Gm.baseChangeIso b).hom) =
      (GroupScheme.baseChange b).map (𝟙 _) ≫ (Gm.baseChangeIso b).hom at h
    simpa only [(GroupScheme.baseChange b).map_id, Category.id_comp] using h
  rwa [transportCharacter, Iso.inv_comp_eq] at h

variable (k K : Type u) [Field k] [Field K] [Algebra k K] [IsGalois k K]
  (T : CommGroupScheme (Spec (CommRingCat.of k))) [IsAffineHom T.X.hom]

/-- Every Galois-invariant character descends: its actual homomorphism descends through
`Descent.GaloisHom.exists_hom`. -/
private theorem character_baseChange_surjective :
    Function.Surjective (characterLattice.baseChangeToInvariants k K T) := by
  intro χ
  let b := algebraBaseMap k K
  let M := (Gm (Spec (CommRingCat.of k))).toGrp
  have : IsAffineHom M.X.hom := isSplitTorus_gm.isAffineHom
  let c : (GroupScheme.baseChange b).obj T.toGrp ⟶ (Gm (Spec (CommRingCat.of K))).toGrp :=
    CommGroupScheme.groupHom χ.val
  let f : (GroupScheme.baseChange b).obj T.toGrp ⟶ (GroupScheme.baseChange b).obj M :=
    c ≫ (Gm.baseChangeIso b).inv
  obtain ⟨f₀, hf₀⟩ := Descent.GaloisHom.exists_hom (k := k) (L := K) f (fun σ => by
    let a := galoisBaseMap k K σ
    let ha : a ≫ b = b := galoisBaseMap_over k K σ
    change (GroupScheme.baseChange a).map f ≫ (descentBaseChangeIso b a ha M).hom =
      (descentBaseChangeIso b a ha T.toGrp).hom ≫ f
    have hfix : (descentBaseChangeIso b a ha T.toGrp).inv ≫
        (GroupScheme.baseChange a).map c ≫ (Gm.baseChangeIso a).hom = c :=
      congrArg CommGroupScheme.groupHom (χ.property σ)
    rw [Iso.inv_comp_eq] at hfix
    have hcmp :
        (GroupScheme.baseChange a).map (Gm.baseChangeIso b).inv ≫
            (descentBaseChangeIso b a ha M).hom ≫ (Gm.baseChangeIso b).hom =
          (Gm.baseChangeIso a).hom := by
      rw [← gm_descent_comparison b a ha, ← Category.assoc, ← Functor.map_comp,
        Iso.inv_hom_id, (GroupScheme.baseChange a).map_id, Category.id_comp]
    apply (cancel_mono (Gm.baseChangeIso b).hom).mp
    simpa only [f, Functor.map_comp, Category.assoc, Iso.inv_hom_id, Category.comp_id, hcmp]
      using hfix)
  refine ⟨Additive.ofMul f₀, Subtype.ext ?_⟩
  change (GroupScheme.baseChange b).map f₀ ≫ (Gm.baseChangeIso b).hom = c
  rw [hf₀]
  dsimp only [f]
  rw [Category.assoc, Iso.inv_hom_id, Category.comp_id]

/-- Every Galois-invariant cocharacter descends: its actual homomorphism descends through
`Descent.GaloisHom.exists_hom`. -/
private theorem cocharacter_baseChange_surjective :
    Function.Surjective (cocharacterLattice.baseChangeToInvariants k K T) := by
  intro ν
  let b := algebraBaseMap k K
  let M := (Gm (Spec (CommRingCat.of k))).toGrp
  have : IsAffineHom M.X.hom := isSplitTorus_gm.isAffineHom
  let c : (Gm (Spec (CommRingCat.of K))).toGrp ⟶ (GroupScheme.baseChange b).obj T.toGrp :=
    CommGroupScheme.groupHom ν.val
  let f : (GroupScheme.baseChange b).obj M ⟶ (GroupScheme.baseChange b).obj T.toGrp :=
    (Gm.baseChangeIso b).hom ≫ c
  obtain ⟨f₀, hf₀⟩ := Descent.GaloisHom.exists_hom (k := k) (L := K) f (fun σ => by
    let a := galoisBaseMap k K σ
    let ha : a ≫ b = b := galoisBaseMap_over k K σ
    change (GroupScheme.baseChange a).map f ≫ (descentBaseChangeIso b a ha T.toGrp).hom =
      (descentBaseChangeIso b a ha M).hom ≫ f
    have hfix : (Gm.baseChangeIso a).inv ≫ (GroupScheme.baseChange a).map c ≫
        (descentBaseChangeIso b a ha T.toGrp).hom = c :=
      congrArg CommGroupScheme.groupHom (ν.property σ)
    rw [Iso.inv_comp_eq] at hfix
    dsimp only [f]
    rw [Functor.map_comp, Category.assoc, hfix,
      ← Category.assoc, gm_descent_comparison b a ha, Category.assoc])
  refine ⟨Additive.ofMul f₀, Subtype.ext ?_⟩
  change (Gm.baseChangeIso b).inv ≫ (GroupScheme.baseChange b).map f₀ = c
  rw [hf₀]
  dsimp only [f]
  rw [Iso.inv_hom_id_assoc]

/-- Base change is bijective onto the invariant character and cocharacter groups. -/
theorem galoisInvariantLattices : GaloisInvariantLatticesStatement.{u} := by
  intro k K _ _ _ _ T _
  exact ⟨⟨characterLattice.baseChangeToInvariants_injective k K T,
      character_baseChange_surjective k K T⟩,
    ⟨cocharacterLattice.baseChangeToInvariants_injective k K T,
      cocharacter_baseChange_surjective k K T⟩⟩

end Langlands.GroupScheme
