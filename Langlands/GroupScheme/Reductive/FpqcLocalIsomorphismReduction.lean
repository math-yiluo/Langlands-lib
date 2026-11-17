import Langlands.GroupScheme.Reductive.FpqcLocalIsomorphismStatement
import Langlands.GroupScheme.Reductive.AffineSplitIsomorphismTheoremStatement
import Langlands.GroupScheme.Reductive.SuppliedToriSimultaneousSplitting
import Langlands.GroupScheme.Reductive.FibrewiseRootDatumComparison
import Mathlib.AlgebraicGeometry.PullbackCarrier

/-! # Reduction of fpqc-local isomorphism to the affine split Isomorphism Theorem -/

noncomputable section

universe u v

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1000000

namespace Langlands.GroupScheme

local instance fpqcLocal_affinePullback {S U : Scheme.{u}} (G : GroupScheme S)
    [IsAffineHom G.X.hom] (b : U ⟶ S) :
    IsAffineHom ((GroupScheme.baseChange b).obj G).X.hom :=
  MorphismProperty.pullback_snd G.X.hom b inferInstance

local instance fpqcLocal_smoothPullback {S U : Scheme.{u}} (G : GroupScheme S)
    [Smooth G.X.hom] (b : U ⟶ S) :
    Smooth ((GroupScheme.baseChange b).obj G).X.hom :=
  MorphismProperty.pullback_snd G.X.hom b inferInstance

/-- Local isomorphisms on any jointly surjective cover give an actual
field-fibre isomorphism above every point of every base change. -/
theorem exists_field_fiber_iso_of_cover
    {S U : Scheme.{u}} {K : Precoverage Scheme.{u}} [Scheme.JointlySurjective K]
    (G H : GroupScheme S) (𝒰 : Scheme.Cover.{v} K S)
    (h𝒰 : ∀ i, Nonempty ((GroupScheme.baseChange (𝒰.f i)).obj G ≅ (GroupScheme.baseChange (𝒰.f i)).obj H))
    (b : U ⟶ S) (x : U) :
    ∃ (k : Type u) (_ : Field k) (c : Spec (CommRingCat.of k) ⟶ U),
      c (IsLocalRing.closedPoint k) = x ∧
      Nonempty ((GroupScheme.baseChange c).obj ((GroupScheme.baseChange b).obj G) ≅
        (GroupScheme.baseChange c).obj ((GroupScheme.baseChange b).obj H)) := by
  obtain ⟨i, y, hy⟩ := 𝒰.exists_eq (b x)
  obtain ⟨w, hw, _⟩ := Scheme.Pullback.exists_preimage_pullback
    (f := b) (g := 𝒰.f i) x y hy.symm
  let W := pullback b (𝒰.f i)
  let r := W.fromSpecResidueField w
  let c := r ≫ pullback.fst b (𝒰.f i)
  let d := r ≫ pullback.snd b (𝒰.f i)
  have he : c ≫ b = d ≫ 𝒰.f i := by
    simp only [c, d, Category.assoc, pullback.condition]
  obtain ⟨e⟩ := h𝒰 i
  have h : Nonempty ((GroupScheme.baseChange (c ≫ b)).obj G ≅ (GroupScheme.baseChange (c ≫ b)).obj H) := by
    rw [he]
    exact ⟨baseChangeCompIso (𝒰.f i) d G ≪≫ (GroupScheme.baseChange d).mapIso e ≪≫
      (baseChangeCompIso (𝒰.f i) d H).symm⟩
  refine ⟨W.residueField w, inferInstance, c, ?_, ?_⟩
  · change pullback.fst b (𝒰.f i) (r _) = x
    rw [Scheme.fromSpecResidueField_apply]
    exact hw
  · obtain ⟨e'⟩ := h
    exact ⟨(baseChangeCompIso b c G).symm ≪≫ e' ≪≫ baseChangeCompIso b c H⟩

/-- The affine split Isomorphism Theorem turns one actual field-fibre
isomorphism into an isomorphism of split reductive groups on the whole affine base. -/
theorem HasSplitMaximalTorusCoordinates.nonempty_iso_of_fieldIso
    (hAffine : AffineSplitIsomorphismTheoremStatement.{u})
    {R : Type u} [CommRing R]
    {G H : GroupScheme (Spec (CommRingCat.of R))}
    [IsAffineHom G.X.hom] [IsAffineHom H.X.hom]
    (hG : IsReductive G) (hH : IsReductive H)
    {T U : CommGroupScheme (Spec (CommRingCat.of R))}
    {i : T.toGrp ⟶ G} {j : U.toGrp ⟶ H}
    (hi : HasSplitMaximalTorusCoordinates i) (hj : HasSplitMaximalTorusCoordinates j)
    (k : Type u) [Field k] (b : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of R))
    (e : (GroupScheme.baseChange b).obj G ≅ (GroupScheme.baseChange b).obj H) : Nonempty (G ≅ H) := by
  let := hG.smooth
  let := hH.smooth
  obtain ⟨I, hI, eI, hc, hm, J, P, hP, hl⟩ := hi
  obtain ⟨I', hI', eI', hc', hm', J', Q, hQ, hl'⟩ := hj
  let : Fintype I := hI
  let : Fintype I' := hI'
  let : Algebra R k := (Spec.preimage b).hom.toAlgebra
  have hb : algebraBaseMap R k = b := Spec.map_preimage b
  have ek : (GroupScheme.baseChange (algebraBaseMap R k)).obj G ≅
      (GroupScheme.baseChange (algebraBaseMap R k)).obj H := by
    simpa only [hb] using e
  obtain ⟨f⟩ := hP.nonempty_equiv_of_reductive_fieldIso hQ hG hH k
    (splitTorus.isMaximalTorus_baseChangeHom_of_fibrewise I G (eI.hom ≫ i) hm k)
    (splitTorus.isMaximalTorus_baseChangeHom_of_fibrewise I' H (eI'.hom ≫ j) hm' k) ek
  obtain ⟨φ, _, _⟩ := hAffine R G H hG hH I I' (eI.hom ≫ i) (eI'.hom ≫ j)
    J J' P Q hc hm hP hl hc' hm' hQ hl' f.symm
  exact ⟨φ⟩

/-- Under the affine split Isomorphism Theorem, locally isomorphic reductive
groups become isomorphic on an affine étale neighbourhood of each base point. -/
theorem exists_etale_affine_iso_of_jointlySurjective_cover
    (hAffine : AffineSplitIsomorphismTheoremStatement.{u})
    (S : Scheme.{u}) (G H : GroupScheme S) (hG : IsReductive G) (hH : IsReductive H)
    {K : Precoverage Scheme.{u}} [Scheme.JointlySurjective K]
    (𝒰 : Scheme.Cover.{v} K S)
    (h𝒰 : ∀ i, Nonempty ((GroupScheme.baseChange (𝒰.f i)).obj G ≅
      (GroupScheme.baseChange (𝒰.f i)).obj H)) (s : S) :
    ∃ (R : Type u) (_ : CommRing R) (f : Spec (CommRingCat.of R) ⟶ S),
      Etale f ∧ (∃ x, f x = s) ∧
      Nonempty ((GroupScheme.baseChange f).obj G ≅ (GroupScheme.baseChange f).obj H) := by
  classical
  let := hG.isAffineHom
  let := hH.isAffineHom
  let := hG.smooth
  let := hH.smooth
  obtain ⟨R, hR, f, hf, ⟨p, hp⟩, I, hI, i, hc, hm, J, P, hP, hl⟩ :=
    etaleLocalSplitReductive S G hG s
  let : CommRing R := hR
  let : Fintype I := hI
  let : Etale f := hf
  let Gf := (GroupScheme.baseChange f).obj G
  let Hf := (GroupScheme.baseChange f).obj H
  have hi : HasSplitMaximalTorusCoordinates (T := splitTorus.commGroupScheme _ I) i := by
    refine ⟨I, hI, Iso.refl _, ?_, ?_, J, P, ?_, ?_⟩
    · simpa only [Iso.refl_hom, Category.id_comp] using hc
    · simpa only [Iso.refl_hom, Category.id_comp] using hm
    · simpa only [Iso.refl_hom, Category.id_comp] using hP
    · intro α
      obtain ⟨l⟩ := hl α
      exact ⟨(LinearEquiv.ofEq _ _ (congrArg
        (fun t => splitTorus.exponentWeightSpace I Gf t (P.root α))
        (Category.id_comp i))).trans l⟩
  obtain ⟨A, hA, a, ha, ⟨q, hq⟩, I', hI', j, hc', hm', J', Q, hQ, hl'⟩ :=
    etaleLocalSplitReductive (Spec (CommRingCat.of R)) Hf (hH.baseChange f) p
  let : CommRing A := hA
  let : Fintype I' := hI'
  let : Etale a := ha
  have hj : HasSplitMaximalTorusCoordinates (T := splitTorus.commGroupScheme _ I') j := by
    refine ⟨I', hI', Iso.refl _, ?_, ?_, J', Q, ?_, ?_⟩
    · simpa only [Iso.refl_hom, Category.id_comp] using hc'
    · simpa only [Iso.refl_hom, Category.id_comp] using hm'
    · simpa only [Iso.refl_hom, Category.id_comp] using hQ
    · intro α
      obtain ⟨l⟩ := hl' α
      exact ⟨(LinearEquiv.ofEq _ _ (congrArg
        (fun t => splitTorus.exponentWeightSpace I' ((GroupScheme.baseChange a).obj Hf)
          t (Q.root α)) (Category.id_comp j))).trans l⟩
  obtain ⟨k, hk, b, _, ⟨e⟩⟩ :=
    exists_field_fiber_iso_of_cover G H 𝒰 h𝒰 (a ≫ f) q
  let : Field k := hk
  let eG := (GroupScheme.baseChange b).mapIso (baseChangeCompIso f a G)
  let eH := (GroupScheme.baseChange b).mapIso (baseChangeCompIso f a H)
  obtain ⟨φ⟩ := (hi.baseChange_affine a).nonempty_iso_of_fieldIso hAffine
    ((hG.baseChange f).baseChange a) ((hH.baseChange f).baseChange a)
    hj k b (eG.symm ≪≫ e ≪≫ eH)
  refine ⟨A, hA, a ≫ f, inferInstance, ⟨q, ?_⟩,
    ⟨baseChangeCompIso f a G ≪≫ φ ≪≫ (baseChangeCompIso f a H).symm⟩⟩
  change f (a q) = s
  rw [hq, hp]

/-- The remaining affine split theorem suffices for fpqc-local isomorphisms
of reductive group schemes over every base in the same universe. -/
def ReductiveFpqcLocalIsomorphismReductionStatement : Prop :=
  AffineSplitIsomorphismTheoremStatement.{u} → ReductiveFpqcLocalIsomorphismStatement.{u}

/-- Assemble the affine étale neighbourhoods into a cover indexed by the
points of the base, starting from the jointly surjective part of the fpqc cover. -/
theorem reductiveFpqcLocalIsomorphism_of_affineSplit :
    ReductiveFpqcLocalIsomorphismReductionStatement.{u} := by
  classical
  intro hAffine S G H hG hH hlocal
  obtain ⟨𝒰, h𝒰⟩ := hlocal
  choose R hR f hf hx hiso using
    exists_etale_affine_iso_of_jointlySurjective_cover hAffine S G H hG hH 𝒰.forgetQc h𝒰
  let 𝒱 : Scheme.Cover.{u} (Scheme.precoverage @Etale) S :=
    Scheme.Cover.mkOfCovers (P := @Etale) (X := S) S
      (fun s => Spec (CommRingCat.of (R s))) f (fun s => ⟨s, hx s⟩) hf
  exact ⟨𝒱, hiso⟩

end Langlands.GroupScheme
