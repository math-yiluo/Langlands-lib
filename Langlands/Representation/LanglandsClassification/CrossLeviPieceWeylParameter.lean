import Langlands.Representation.LanglandsClassification.UnramifiedPieceWeylParameter

/-! # The Weyl parameter of a geometric-lemma piece between two Levis -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry TensorProduct
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

variable {k : Type u} [Field k]
  {G M L : GroupScheme (Spec (CommRingCat.of k))}
  {T S : CommGroupScheme (Spec (CommRingCat.of k))}

/-- A common maximal split torus occurring in two connected reductive closed subgroups
`M` and `L`, with the two occurrences conjugate by `z`, corrects `z` to a normalizer
representative by a left factor in `M` and a right factor in `L`. -/
theorem exists_normalizerPoint_of_commonSplitTorus_two
    (hM : IsConnectedReductive M) (hL : IsConnectedReductive L)
    (j : M ⟶ G) (hj : IsClosedSubgroup j) (jL : L ⟶ G) (hjL : IsClosedSubgroup jL)
    (i : T.toGrp ⟶ G) (hi : IsMaximalSplitTorus i)
    (iM : T.toGrp ⟶ M) (hiM : iM ≫ j = i) (iL : T.toGrp ⟶ L) (hiL : iL ≫ jL = i)
    (s : S.toGrp ⟶ M) (t : S.toGrp ⟶ L)
    (hs : IsMaximalSplitTorus (s ≫ j)) (ht : IsMaximalSplitTorus (t ≫ jL))
    (z : rationalPoints G) (hst : s ≫ j = t ≫ jL ≫ (G.innerIso z).hom) :
    ∃ (mS : rationalPoints M) (mT : rationalPoints L) (n : normalizerPoints i),
      n.val = (mS ≫ j.hom.hom) * z * (mT ≫ jL.hom.hom)⁻¹ := by
  have hiM' : IsMaximalSplitTorus iM :=
    IsMaximalSplitTorus.of_comp hj (hiM.symm ▸ hi)
  have hiL' : IsMaximalSplitTorus iL :=
    IsMaximalSplitTorus.of_comp hjL (hiL.symm ▸ hi)
  have hsM : IsMaximalSplitTorus s := IsMaximalSplitTorus.of_comp hj hs
  have htL : IsMaximalSplitTorus t := IsMaximalSplitTorus.of_comp hjL ht
  obtain ⟨mS, eS, heS⟩ := (maximalSplitTorusConjugacy k M hM).1 S T s iM hsM hiM'
  obtain ⟨mT, eT, heT⟩ := (maximalSplitTorusConjugacy k L hL).1 S T t iL htL hiL'
  have heS' : (s ≫ j) ≫ (G.innerIso (mS ≫ j.hom.hom)).hom = eS.hom ≫ i := by
    rw [Category.assoc, ← innerIso_hom_comp, ← Category.assoc, heS,
      Category.assoc, hiM]
  have heT' : (t ≫ jL) ≫ (G.innerIso (mT ≫ jL.hom.hom)).hom = eT.hom ≫ i := by
    rw [Category.assoc, ← innerIso_hom_comp, ← Category.assoc, heT,
      Category.assoc, hiL]
  have heTinv : i ≫ (G.innerIso (mT ≫ jL.hom.hom)⁻¹).hom = eT.inv ≫ (t ≫ jL) := by
    rw [innerIso_inv_hom, Iso.comp_inv_eq, Category.assoc, heT',
      Iso.inv_hom_id_assoc]
  let e : T.toGrp ≅ T.toGrp := eT.symm ≪≫ eS
  let σ : T ≅ T :=
    { hom := Additive.ofMul e.hom
      inv := Additive.ofMul e.inv
      hom_inv_id := congrArg Additive.ofMul e.hom_inv_id
      inv_hom_id := congrArg Additive.ofMul e.inv_hom_id }
  have hn : IsNormalizingPoint i
      ((mS ≫ j.hom.hom) * z * (mT ≫ jL.hom.hom)⁻¹) σ := by
    change i ≫ (G.innerIso
      ((mS ≫ j.hom.hom) * z * (mT ≫ jL.hom.hom)⁻¹)).hom =
        (eT.inv ≫ eS.hom) ≫ i
    calc
      _ = (i ≫ (G.innerIso (mT ≫ jL.hom.hom)⁻¹).hom) ≫
          (G.innerIso z).hom ≫ (G.innerIso (mS ≫ j.hom.hom)).hom := by
        simp only [innerIso_mul_hom, Category.assoc]
      _ = eT.inv ≫ (t ≫ jL ≫ (G.innerIso z).hom) ≫
          (G.innerIso (mS ≫ j.hom.hom)).hom := by
        rw [heTinv]
        simp only [Category.assoc]
      _ = eT.inv ≫ ((s ≫ j) ≫ (G.innerIso (mS ≫ j.hom.hom)).hom) := by
        rw [← hst]
      _ = (eT.inv ≫ eS.hom) ≫ i := by
        rw [heS', Category.assoc]
  exact ⟨mS, mT, ⟨_, ⟨σ, hn⟩⟩, rfl⟩

variable {A : CommGroupScheme (Spec (CommRingCat.of k))}

/-- For a central component `a` of `L`, a map `b` into `M` conjugate to it by `z`
differs from the normalizer pullback only by an inner automorphism of `M`. -/
theorem comp_innerIso_eq_normalizer_pullback_two
    (j : M ⟶ G) (hj : IsClosedSubgroup j) (jL : L ⟶ G)
    (i : T.toGrp ⟶ G) (iM : T.toGrp ⟶ M) (hiM : iM ≫ j = i)
    (iL : T.toGrp ⟶ L) (hiL : iL ≫ jL = i)
    (a : A.toGrp ⟶ L) (b : A.toGrp ⟶ M) (ha : IsCentral a)
    (f : A ⟶ T) (hf : CommGroupScheme.groupHom f ≫ iL = a)
    (z : rationalPoints G) (hb : b ≫ j = a ≫ jL ≫ (G.innerIso z).hom)
    (mS : rationalPoints M) (mT : rationalPoints L) (n : normalizerPoints i)
    (hn : n.val = (mS ≫ j.hom.hom) * z * (mT ≫ jL.hom.hom)⁻¹) :
    b ≫ (M.innerIso mS).hom =
      CommGroupScheme.groupHom (f ≫ (normalizingAut i n).hom) ≫ iM := by
  have hinv : (mT ≫ jL.hom.hom)⁻¹ = mT⁻¹ ≫ jL.hom.hom :=
    (map_inv (rationalPoints.map jL) mT).symm
  have hc : a ≫ jL ≫ (G.innerIso (mT ≫ jL.hom.hom)⁻¹).hom = a ≫ jL := by
    rw [hinv, ← innerIso_hom_comp, ← Category.assoc, ha.comp_innerIso_hom]
  have hconj : a ≫ jL ≫ (G.innerIso n.val).hom =
      (b ≫ (M.innerIso mS).hom) ≫ j := by
    calc
      _ = (a ≫ jL ≫ (G.innerIso (mT ≫ jL.hom.hom)⁻¹).hom) ≫
          (G.innerIso z).hom ≫ (G.innerIso (mS ≫ j.hom.hom)).hom := by
        rw [hn]
        simp only [innerIso_mul_hom, Category.assoc]
      _ = (a ≫ jL ≫ (G.innerIso z).hom) ≫
          (G.innerIso (mS ≫ j.hom.hom)).hom := by
        rw [hc]
        simp only [Category.assoc]
      _ = (b ≫ j) ≫ (G.innerIso (mS ≫ j.hom.hom)).hom := by rw [hb]
      _ = (b ≫ (M.innerIso mS).hom) ≫ j := by
        rw [Category.assoc, ← innerIso_hom_comp, ← Category.assoc]
  have hnorm : (CommGroupScheme.groupHom (f ≫ (normalizingAut i n).hom) ≫ iM) ≫ j =
      (b ≫ (M.innerIso mS).hom) ≫ j := by
    calc
      _ = CommGroupScheme.groupHom f ≫
          CommGroupScheme.groupHom (normalizingAut i n).hom ≫ i := by
        change ((CommGroupScheme.groupHom f ≫
          CommGroupScheme.groupHom (normalizingAut i n).hom) ≫ iM) ≫ j = _
        simp only [Category.assoc, hiM]
      _ = CommGroupScheme.groupHom f ≫ i ≫ (G.innerIso n.val).hom := by
        rw [← isNormalizingPoint_normalizingAut i n]
      _ = a ≫ jL ≫ (G.innerIso n.val).hom := by
        have hfi : CommGroupScheme.groupHom f ≫ i = a ≫ jL := by
          rw [← hiL, ← Category.assoc, hf]
        simpa only [Category.assoc] using
          congrArg (fun g => g ≫ (G.innerIso n.val).hom) hfi
      _ = _ := hconj
  let := hj.mono
  let : Mono j.hom.hom := Over.mono_of_mono_left _
  apply Grp.hom_ext
  apply (cancel_mono j.hom.hom).mp
  exact congrArg (fun g => g.hom.hom) hnorm.symm

/-- Characters of `M` erase the inner conjugacy in the corrected map. -/
theorem character_comp_eq_of_normalizerCorrection_two
    (j : M ⟶ G) (hj : IsClosedSubgroup j) (jL : L ⟶ G)
    (i : T.toGrp ⟶ G) (iM : T.toGrp ⟶ M) (hiM : iM ≫ j = i)
    (iL : T.toGrp ⟶ L) (hiL : iL ≫ jL = i)
    (a : A.toGrp ⟶ L) (b : A.toGrp ⟶ M) (ha : IsCentral a)
    (f : A ⟶ T) (hf : CommGroupScheme.groupHom f ≫ iL = a)
    (z : rationalPoints G) (hb : b ≫ j = a ≫ jL ≫ (G.innerIso z).hom)
    (mS : rationalPoints M) (mT : rationalPoints L) (n : normalizerPoints i)
    (hn : n.val = (mS ≫ j.hom.hom) * z * (mT ≫ jL.hom.hom)⁻¹)
    (χ : rationalPoints M →* ℂˣ) :
    χ.comp (rationalPoints.map b) =
      χ.comp (rationalPoints.map
        (CommGroupScheme.groupHom (f ≫ (normalizingAut i n).hom) ≫ iM)) := by
  rw [← comp_innerIso_eq_normalizer_pullback_two j hj jL i iM hiM iL hiL a b ha f hf z hb
    mS mT n hn]
  apply MonoidHom.ext
  intro x
  change χ (x ≫ b.hom.hom) =
    χ ((x ≫ b.hom.hom) ≫ (M.innerIso mS).hom.hom.hom)
  rw [comp_innerIso_hom, constantPoint_self, map_mul, map_mul, map_inv]
  exact (mul_inv_cancel_comm _ _).symm

end Langlands.GroupScheme

namespace Langlands.Aubert.General.RepresentedParabolic

open GroupScheme

namespace GeometricLemmaIntersectionDatum

variable {k : Type u} [Field k] [TopologicalSpace k]
  {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
  {P M N Q L U : GroupScheme (Spec (CommRingCat.of k))}
  {p : P ⟶ G} {l : M ⟶ P} {r : N ⟶ P}
  {hp : IsParabolicSubgroup p} {hr : LeviSubgroup.IsGeometricUnipotentRadical r}
  {hl : IsRationalLeviSubgroup l} {hmul : IsIso (subgroupMultiplication l r)}
  {q : Q ⟶ G} {lQ : L ⟶ Q} {rQ : U ⟶ Q}
  {hq : IsParabolicSubgroup q} {hrQ : LeviSubgroup.IsGeometricUnipotentRadical rQ}
  {hlQ : IsRationalLeviSubgroup lQ} {hmulQ : IsIso (subgroupMultiplication lQ rQ)}
  {z : rationalPoints G}
  (D : GeometricLemmaIntersectionDatum p l r hp hr hl hmul
    q lQ rQ hq hrQ hlQ hmulQ z)
  {AM A : CommGroupScheme (Spec (CommRingCat.of k))} {aM : AM.toGrp ⟶ M}
  (pres : ParabolicRootPresentation p l aM)

include D in
/-- An intersection datum for two parabolics with possibly different Levis `M` and `L`
has a normalizer representative `mS z mT⁻¹` of the fixed maximal split torus, with
`mS ∈ M(k)` and `mT ∈ L(k)`, whenever that torus also lies in `L`. -/
theorem exists_normalizerPoint_crossLevi
    (iL : pres.data.T.toGrp ⟶ L) (hiL : iL ≫ lQ ≫ q = pres.data.i) :
    ∃ (mS : rationalPoints M) (mT : rationalPoints L) (n : normalizerPoints pres.data.i),
      n.val = (mS ≫ (l ≫ p).hom.hom) * z * (mT ≫ (lQ ≫ q).hom.hom)⁻¹ := by
  have hst : (D.t ≫ D.l' ≫ D.p') ≫ (l ≫ p) =
      (D.targetCommonTorusHom ≫ D.lQ' ≫ D.q') ≫
        (lQ ≫ q) ≫ (G.innerIso z).hom := by
    have h := congrArg (fun g => g ≫ (G.innerIso z).hom) D.targetCommonTorusHom_comp
    simpa only [Category.assoc, Iso.inv_hom_id, Category.comp_id] using h.symm
  apply exists_normalizerPoint_of_commonSplitTorus_two hl.isConnectedReductive
    hlQ.isConnectedReductive
    (l ≫ p) (hl.isClosedSubgroup.comp hp.isClosedSubgroup)
    (lQ ≫ q) (hlQ.isClosedSubgroup.comp hq.isClosedSubgroup)
    pres.data.i pres.isCompatible.maximalSplit pres.leviTorusHom
    pres.leviTorusHom_comp iL hiL (D.t ≫ D.l' ≫ D.p')
    (D.targetCommonTorusHom ≫ D.lQ' ≫ D.q')
  · simpa only [Category.assoc] using D.isMaximalSplitTorus
  · simpa only [Category.assoc] using D.targetCommonTorus_isMaximalSplitTorus_ambient
  · exact hst

/-- A character of `M` pulled back by the piece maps equals its pullback through the
normalizer-twisted torus factor. -/
theorem character_comp_piece_eq_normalizerPullback_crossLevi
    (iL : pres.data.T.toGrp ⟶ L) (hiL : iL ≫ lQ ≫ q = pres.data.i)
    {a : A.toGrp ⟶ L} (ha : IsCentral a) (f : A ⟶ pres.data.T)
    (hf : CommGroupScheme.groupHom f ≫ iL = a)
    (b : A.toGrp ⟶ D.L') (hb : b ≫ D.lQ' ≫ D.q' = a)
    (mS : rationalPoints M) (mT : rationalPoints L) (n : normalizerPoints pres.data.i)
    (hn : n.val = (mS ≫ (l ≫ p).hom.hom) * z * (mT ≫ (lQ ≫ q).hom.hom)⁻¹)
    (χ : rationalPoints M →* ℂˣ) :
    χ.comp (rationalPoints.map (b ≫ D.φ.hom ≫ D.l' ≫ D.p')) =
      χ.comp (rationalPoints.map
        (CommGroupScheme.groupHom (f ≫ (normalizingAut pres.data.i n).hom) ≫
          pres.leviTorusHom)) := by
  apply character_comp_eq_of_normalizerCorrection_two (l ≫ p)
    (hl.isClosedSubgroup.comp hp.isClosedSubgroup) (lQ ≫ q)
    pres.data.i pres.leviTorusHom pres.leviTorusHom_comp iL hiL
    a (b ≫ D.φ.hom ≫ D.l' ≫ D.p') ha f hf z
  · calc
      _ = b ≫ (D.φ.hom ≫ D.l' ≫ D.p' ≫ l ≫ p) := by
        simp only [Category.assoc]
      _ = b ≫ D.lQ' ≫ D.q' ≫ (lQ ≫ q) ≫ (G.innerIso z).hom := by
        rw [D.φ_comp]
        simp only [Category.assoc]
      _ = a ≫ (lQ ≫ q) ≫ (G.innerIso z).hom := by
        simpa only [Category.assoc] using
          congrArg (fun g => g ≫ (lQ ≫ q) ≫ (G.innerIso z).hom) hb
  · exact hn

section RealPart

variable [ValuativeRel k] [IsNonarchimedeanLocalField k]

open Langlands.AlgebraicGeometry.PointTopology

local instance : Mono pres.data.i.hom.hom.left :=
  pres.isCompatible.maximalSplit.isSplitSubtorus.mono

local instance : IsAffineHom pres.data.T.X.hom :=
  pres.isCompatible.maximalSplit.isSplitSubtorus.1.isAffineHom

local instance : IsAffine pres.data.T.X.left :=
  isAffine_of_isAffineHom pres.data.T.X.hom

local instance : TopologicalSpace (rationalPoints pres.data.T.toGrp) :=
  rationalPointTopology k pres.data.T.X

/-- The real part of an unramified character of `M`, pulled back by the piece maps to a
split component `a` of the other Levi `L`, is the restriction along `f` of a relative
Weyl translate of the full real parameter of the character. -/
theorem exists_normalizedRealPart_piece_eq_weyl_crossLevi
    (iL : pres.data.T.toGrp ⟶ L) (hiL : iL ≫ lQ ≫ q = pres.data.i)
    {a : A.toGrp ⟶ L} (ha : IsSplitComponent a) (f : A ⟶ pres.data.T)
    (hf : CommGroupScheme.groupHom f ≫ iL = a)
    (b : A.toGrp ⟶ D.L') (hb : b ≫ D.lQ' ≫ D.q' = a)
    (ψ : leviUnramifiedCharacters l hl) :
    letI := leviPointTopology l hl
    ∃ w : relativeWeylGroup pres.data.i,
      Plancherel.SplitTorus.normalizedRealPart ha.isCentralSplitTorus.1.1
          (ψ.val.toMonoidHom.comp
            (rationalPoints.map (b ≫ D.φ.hom ≫ D.l' ≫ D.p'))) =
        rationalCharacterRestrictReal (CommGroupScheme.groupHom f)
          (relativeWeylFullRealAction pres.data.i w (leviUnramifiedFullRealPart pres ψ)) := by
  let := leviPointTopology l hl
  obtain ⟨mS, mT, n, hn⟩ := D.exists_normalizerPoint_crossLevi pres iL hiL
  refine ⟨(QuotientGroup.mk n)⁻¹, ?_⟩
  let χT := ψ.val.toMonoidHom.comp (rationalPoints.map pres.leviTorusHom)
  let σ := normalizingAut pres.data.i n
  have hT := pres.isCompatible.maximalSplit.isSplitSubtorus.1
  have hχT : IsOpen (χT.ker : Set (rationalPoints pres.data.T.toGrp)) :=
    isOpen_ker_leviUnramifiedTorusCharacter pres ψ
  have hχσ := Plancherel.SplitTorus.isOpen_ker_comp_points σ.hom χT hχT
  have hσinv : normalizingAut pres.data.i n⁻¹ = σ.symm :=
    (isNormalizingPoint_normalizingAut pres.data.i n⁻¹).unique pres.data.i
      (isNormalizingPoint_normalizingAut pres.data.i n).inv
  have hreal : Plancherel.SplitTorus.normalizedRealPart hT
      (χT.comp (rationalPoints.map (CommGroupScheme.groupHom σ.hom))) =
      relativeWeylFullRealAction pres.data.i
        ((QuotientGroup.mk n)⁻¹) (leviUnramifiedFullRealPart pres ψ) := by
    change _ = relativeWeylFullRealAction pres.data.i
      (QuotientGroup.mk n⁻¹) (leviUnramifiedFullRealPart pres ψ)
    rw [relativeWeylFullRealAction_mk, hσinv]
    exact Plancherel.SplitTorus.normalizedRealPart_comp_points hT hT σ.hom χT hχT
  have hchar : ψ.val.toMonoidHom.comp
      (rationalPoints.map (b ≫ D.φ.hom ≫ D.l' ≫ D.p')) =
      (χT.comp (rationalPoints.map (CommGroupScheme.groupHom σ.hom))).comp
        (rationalPoints.map (CommGroupScheme.groupHom f)) := by
    rw [D.character_comp_piece_eq_normalizerPullback_crossLevi pres iL hiL
      ha.isCentralSplitTorus.isCentral f hf b hb mS mT n hn]
    apply MonoidHom.ext
    intro x
    change ψ.val (x ≫ ((CommGroupScheme.groupHom f ≫
      CommGroupScheme.groupHom σ.hom) ≫ pres.leviTorusHom).hom.hom) =
      ψ.val (((x ≫ (CommGroupScheme.groupHom f).hom.hom) ≫
        (CommGroupScheme.groupHom σ.hom).hom.hom) ≫ pres.leviTorusHom.hom.hom)
    simp only [Grp.comp_hom_hom, Category.assoc]
  rw [hchar, Plancherel.SplitTorus.normalizedRealPart_comp_points
    ha.isCentralSplitTorus.1.1 hT f _ hχσ, hreal]

end RealPart

end GeometricLemmaIntersectionDatum

end Langlands.Aubert.General.RepresentedParabolic
