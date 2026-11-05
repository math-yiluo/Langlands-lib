import Langlands.GroupScheme.Rational.SplitTorusCharacterDescent
import Langlands.GroupScheme.Absolute.CocharacterDescentGroup

/-! # Descent of maps into split tori from descent of characters -/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj CategoryTheory.Obj

namespace Langlands.GroupScheme

namespace splitTorus

variable {S S' : Scheme.{u}} (b : S' ⟶ S) (I : Type u) [Finite I]

/-- Every coordinate projection commutes with the actual split-torus
base-change isomorphism, in the category of group schemes. -/
theorem baseChangeIso_hom_π (i : I) :
    (baseChangeIso b I).hom ≫ (Pi.π (fun _ : I => (Gm S').toGrp) i) =
      (GroupScheme.baseChange b).map (Pi.π (fun _ : I => (Gm S).toGrp) i) ≫
        (Gm.baseChangeIso b).hom := by
  exact congrArg CommGroupScheme.groupHom (commBaseChangeIso_hom_proj b I i)

variable {H : GroupScheme S}

/-- A map into a coordinate split torus descends if all characters of its
source descend. -/
theorem exists_hom_of_characterSurjective
    (hchar : Function.Surjective
      (fun χ : H ⟶ (Gm S).toGrp =>
        (GroupScheme.baseChange b).map χ ≫ (Gm.baseChangeIso b).hom))
    (g : (GroupScheme.baseChange b).obj H ⟶ splitTorus S' I) :
    ∃ f : H ⟶ splitTorus S I,
      (GroupScheme.baseChange b).map f ≫ (baseChangeIso b I).hom = g := by
  classical
  choose χ hχ using fun i : I =>
    hchar (g ≫ Pi.π (fun _ : I => (Gm S').toGrp) i)
  refine ⟨Pi.lift χ, ?_⟩
  apply Pi.hom_ext
  intro i
  rw [Category.assoc, baseChangeIso_hom_π, ← Functor.map_comp_assoc,
    Pi.lift_comp_π]
  exact hχ i

end splitTorus

variable {S S' : Scheme.{u}} (b : S' ⟶ S) {H D : GroupScheme S}

/-- Descent of characters of the source gives descent of every homomorphism
to a supplied ground-field split torus. -/
theorem IsSplitTorus.hom_baseChange_surjective_of_characterSurjective
    (hD : IsSplitTorus D)
    (hchar : Function.Surjective
      (fun χ : H ⟶ (Gm S).toGrp =>
        (GroupScheme.baseChange b).map χ ≫ (Gm.baseChangeIso b).hom)) :
    Function.Surjective
      (fun f : H ⟶ D => (GroupScheme.baseChange b).map f) := by
  obtain ⟨I, hI, ⟨e⟩⟩ := hD
  intro g
  obtain ⟨f, hf⟩ := splitTorus.exists_hom_of_characterSurjective b I hchar
    (g ≫ (GroupScheme.baseChange b).map e.hom ≫ (splitTorus.baseChangeIso b I).hom)
  refine ⟨f ≫ e.inv, ?_⟩
  have hf' : (GroupScheme.baseChange b).map f =
      g ≫ (GroupScheme.baseChange b).map e.hom :=
    (cancel_mono (splitTorus.baseChangeIso b I).hom).mp hf
  change (GroupScheme.baseChange b).map (f ≫ e.inv) = g
  rw [Functor.map_comp, hf', Category.assoc, ← Functor.map_comp,
    Iso.hom_inv_id, CategoryTheory.Functor.map_id, Category.comp_id]

variable {k K : Type u} [Field k] [Field K] [Algebra k K]
    {G T : GroupScheme (Spec (CommRingCat.of k))}

/-- Over a field extension, descended characters give unique descent of
every map to a supplied split torus. -/
theorem IsSplitTorus.existsUnique_hom_of_characterSurjective
    (hT : IsSplitTorus T)
    (hchar : Function.Surjective
      (fun χ : G ⟶ (Gm (Spec (CommRingCat.of k))).toGrp =>
        (GroupScheme.baseChange (algebraBaseMap k K)).map χ ≫
          (Gm.baseChangeIso (algebraBaseMap k K)).hom))
    (g : (GroupScheme.baseChange (algebraBaseMap k K)).obj G ⟶
      (GroupScheme.baseChange (algebraBaseMap k K)).obj T) :
    ∃! f : G ⟶ T, (GroupScheme.baseChange (algebraBaseMap k K)).map f = g := by
  obtain ⟨f, hf⟩ := hT.hom_baseChange_surjective_of_characterSurjective
    (algebraBaseMap k K) hchar g
  refine ⟨f, hf, ?_⟩
  intro f' hf'
  let := GaloisCocharacterDescent.faithful_algebraPullback k K
  apply Grp.hom_ext
  apply (Over.pullback (algebraBaseMap k K)).map_injective
  exact congrArg (fun q => q.hom.hom) (hf'.trans hf.symm)

variable [IsReduced G.X.left] [IsAffineHom G.X.hom]

/-- For a reduced affine group with pointed split-torus domination, actual
homomorphisms to any supplied split torus are unchanged by field extension. -/
theorem HasPointedSplitTorusDomination.splitTorusHom_baseChange_bijective
    (hG : HasPointedSplitTorusDomination G) (hT : IsSplitTorus T) :
    Function.Bijective
      (fun f : G ⟶ T =>
        (GroupScheme.baseChange (algebraBaseMap k K)).map f) := by
  refine ⟨?_, ?_⟩
  · intro f f' he
    let := GaloisCocharacterDescent.faithful_algebraPullback k K
    apply Grp.hom_ext
    apply (Over.pullback (algebraBaseMap k K)).map_injective
    exact congrArg (fun q => q.hom.hom) he
  · exact hT.hom_baseChange_surjective_of_characterSurjective
      (algebraBaseMap k K) (fun χ => hG.exists_character χ)

/-- The actual Hom equivalence for a split target; its inverse descends
extension-field homomorphisms to the ground field. -/
def HasPointedSplitTorusDomination.splitTorusHomEquiv
    (hG : HasPointedSplitTorusDomination G) (hT : IsSplitTorus T) :
    (G ⟶ T) ≃
      ((GroupScheme.baseChange (algebraBaseMap k K)).obj G ⟶
        (GroupScheme.baseChange (algebraBaseMap k K)).obj T) :=
  Equiv.ofBijective
    (fun f => (GroupScheme.baseChange (algebraBaseMap k K)).map f)
    (hG.splitTorusHom_baseChange_bijective hT)

/-- The forward equivalence is actual base change. -/
@[simp]
theorem HasPointedSplitTorusDomination.splitTorusHomEquiv_apply
    (hG : HasPointedSplitTorusDomination G) (hT : IsSplitTorus T) (f : G ⟶ T) :
    hG.splitTorusHomEquiv (K := K) hT f =
      (GroupScheme.baseChange (algebraBaseMap k K)).map f := rfl

/-- The descended homomorphism recovers the supplied extension-field map. -/
@[simp]
theorem HasPointedSplitTorusDomination.baseChange_splitTorusHomEquiv_symm
    (hG : HasPointedSplitTorusDomination G) (hT : IsSplitTorus T)
    (g : (GroupScheme.baseChange (algebraBaseMap k K)).obj G ⟶
      (GroupScheme.baseChange (algebraBaseMap k K)).obj T) :
    (GroupScheme.baseChange (algebraBaseMap k K)).map
      ((hG.splitTorusHomEquiv (K := K) hT).symm g) = g :=
  (hG.splitTorusHomEquiv (K := K) hT).apply_symm_apply g

/-- Descent of a homomorphism to a supplied split torus is unique. -/
theorem HasPointedSplitTorusDomination.existsUnique_splitTorusHom
    (hG : HasPointedSplitTorusDomination G) (hT : IsSplitTorus T)
    (g : (GroupScheme.baseChange (algebraBaseMap k K)).obj G ⟶
      (GroupScheme.baseChange (algebraBaseMap k K)).obj T) :
    ∃! f : G ⟶ T, (GroupScheme.baseChange (algebraBaseMap k K)).map f = g :=
  hT.existsUnique_hom_of_characterSurjective (fun χ => hG.exists_character χ) g

end Langlands.GroupScheme
