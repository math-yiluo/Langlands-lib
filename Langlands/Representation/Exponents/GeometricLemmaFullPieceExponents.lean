import Langlands.Representation.Exponents.GeometricLemmaExponentTransfer
import Langlands.Representation.Exponents.JacquetExponentRestriction
import Langlands.Representation.Exponents.FullParabolicExponentCone

/-! # Exponents of the full pieces of the represented geometric lemma

For a geometric-lemma datum of `(P, Q)` whose source parabolic `P' = M ∩ zQz⁻¹` and target
parabolic `Q' = L ∩ z⁻¹Pz` are both full, every exponent of the piece at `σ` takes, at each
split-component point, the scalar by which the transported point acts on `σ`. The scalar
action is a hypothesis; over a nonarchimedean local field, Schur's lemma supplies it for an
irreducible `σ`, as its central character at the transported point. The general central-value lemma below needs only a scalar action of one central point, not a
unitary central character.
-/

noncomputable section

universe u v uG uV uB

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.Aubert.General

section CentralScalars

variable {Γ : Type uG} [Group Γ] [TopologicalSpace Γ]
  [LocallyCompactSpace Γ] [NonarchimedeanGroup Γ]

/-- A normalized Jacquet generalized eigencharacter takes, at a point whose actual ambient
image is central, the scalar by which that point acts on the original representation. -/
theorem normalizedJacquet_generalizedEigencharacter_apply_eq_of_smul
    {B : Type uB} [Group B]
    (N L : Subgroup Γ) (hN : IsClosed (N : Set Γ))
    (hLN : L ≤ Subgroup.normalizer (N : Set Γ))
    (π : SmoothRep.{0, uG, uV} ℂ Γ) (z : B →* L) (χ : B →* ℂˣ)
    (hχ : IsGeneralizedEigencharacter
      (((normalizedJacquetFunctor N L hN hLN).obj π).representation.comp z) χ)
    (b : B) (hb : (z b : Γ) ∈ Subgroup.center Γ) (s : ℂ)
    (hs : ∀ v : π, π.representation (z b : Γ) v = s • v) :
    (χ b : ℂ) = s := by
  obtain ⟨d, v, hv, hd⟩ := (isGeneralizedEigencharacter_iff _ _).mp hχ
  have hscalar :
      ((normalizedJacquetFunctor N L hN hLN).obj π).representation (z b) = s • 1 := by
    ext w
    obtain ⟨w', rfl⟩ := Jacquet.Localization.mk_surjective π.representation N 1 w
    rw [normalizedJacquetFunctor_obj_apply_of_mem_center N L hN hLN π (z b) hb, hs, map_smul]
    rfl
  have hpow := hd b
  change (((((normalizedJacquetFunctor N L hN hLN).obj π).representation (z b) -
    (χ b : ℂ) • 1) ^ d) v) = 0 at hpow
  have hzero : (s - (χ b : ℂ)) ^ d • v = 0 := by
    simpa only [hscalar, ← sub_smul, smul_pow, one_pow, LinearMap.smul_apply,
      Module.End.one_apply] using hpow
  exact (sub_eq_zero.mp (eq_zero_of_pow_eq_zero
    ((smul_eq_zero.mp hzero).resolve_right hv))).symm

end CentralScalars

/-- Statement form of `normalizedJacquet_generalizedEigencharacter_apply_eq_of_smul`: over
every locally compact nonarchimedean group, a generalized eigencharacter `χ` of a normalized
Jacquet module along `z : B →* L` takes, at a point `b` with `z b` central, the scalar by
which `z b` acts on the original representation. -/
def NormalizedJacquetCentralScalarStatement : Prop :=
  ∀ (Γ : Type uG) [Group Γ] [TopologicalSpace Γ] [LocallyCompactSpace Γ]
    [NonarchimedeanGroup Γ] (B : Type uB) [Group B] (N L : Subgroup Γ)
    (hN : IsClosed (N : Set Γ)) (hLN : L ≤ Subgroup.normalizer (N : Set Γ))
    (π : SmoothRep.{0, uG, uV} ℂ Γ) (z : B →* L) (χ : B →* ℂˣ),
    IsGeneralizedEigencharacter
        (((normalizedJacquetFunctor N L hN hLN).obj π).representation.comp z) χ →
      ∀ b : B, (z b : Γ) ∈ Subgroup.center Γ → ∀ s : ℂ,
        (∀ v : π, π.representation (z b : Γ) v = s • v) → (χ b : ℂ) = s

theorem normalizedJacquetCentralScalar : NormalizedJacquetCentralScalarStatement.{uG, uV, uB} :=
  fun _ _ _ _ _ _ _ N L hN hLN π z χ hχ b hb s hs =>
    normalizedJacquet_generalizedEigencharacter_apply_eq_of_smul N L hN hLN π z χ hχ b hb s hs

namespace RepresentedParabolic

open GroupScheme

section Exponent

variable {k : Type u} [Field k] [TopologicalSpace k] [T2Space k]
  {G P M U : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]

local instance fullPieceExponentPointTopology : TopologicalSpace (rationalPoints G) :=
  RationalPointFamily.pointTopology

variable [LocallyCompactSpace (rationalPoints G)] [NonarchimedeanGroup (rationalPoints G)]
  (p : P ⟶ G) (l : M ⟶ P) (r : U ⟶ P)
  (hp : IsParabolicSubgroup p) (hl : IsRationalLeviSubgroup l)
  (hr : LeviSubgroup.IsGeometricUnipotentRadical r)
  (hmul : IsIso (subgroupMultiplication l r))
  {A : CommGroupScheme (Spec (CommRingCat.of k))} {a : A.toGrp ⟶ M}

/-- An actual normalized Jacquet exponent takes, at a split-component point with central
ambient image, the scalar by which that point acts on the representation. -/
theorem normalizedJacquetExponent_apply_eq_of_smul (ha : IsSplitComponent a)
    (π : SmoothRep.{0, u, v} ℂ (rationalPoints G)) (χ : rationalPoints A.toGrp →* ℂˣ)
    (hχ : IsNormalizedJacquetExponent p l r hp hl hr hmul ha π χ)
    (t : rationalPoints A.toGrp)
    (ht : (splitComponentPointsMap (l ≫ p) a t : rationalPoints G) ∈
      Subgroup.center (rationalPoints G)) (s : ℂ)
    (hs : ∀ v : π,
      π.representation (splitComponentPointsMap (l ≫ p) a t : rationalPoints G) v = s • v) :
    (χ t : ℂ) = s :=
  normalizedJacquet_generalizedEigencharacter_apply_eq_of_smul
    (pointImage (r ≫ p)) (pointImage (l ≫ p))
    (isClosed_pointImage_comp p r hp.isClosedSubgroup hr.1.isClosedSubgroup)
    (pointImage_le_normalizer p l r hr) π (splitComponentPointsMap (l ≫ p) a) χ
    ((isNormalizedJacquetExponent_iff p l r hp hl hr hmul ha π χ).mp hχ) t ht s hs

end Exponent

namespace GeometricLemmaIntersectionDatum

variable {k : Type u} [Field k] [TopologicalSpace k] [T2Space k]
  {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]

local instance fullPieceAmbientPointTopology : TopologicalSpace (rationalPoints G) :=
  RationalPointFamily.pointTopology

variable [LocallyCompactSpace (rationalPoints G)] [NonarchimedeanGroup (rationalPoints G)]
  {P M N Q L U : GroupScheme (Spec (CommRingCat.of k))}
  {p : P ⟶ G} {l : M ⟶ P} {r : N ⟶ P} {hp : IsParabolicSubgroup p}
  {hr : LeviSubgroup.IsGeometricUnipotentRadical r} {hl : IsRationalLeviSubgroup l}
  {hmul : IsIso (subgroupMultiplication l r)}
  {q : Q ⟶ G} {lQ : L ⟶ Q} {rQ : U ⟶ Q} {hq : IsParabolicSubgroup q}
  {hrQ : LeviSubgroup.IsGeometricUnipotentRadical rQ} {hlQ : IsRationalLeviSubgroup lQ}
  {hmulQ : IsIso (subgroupMultiplication lQ rQ)} {z : rationalPoints G}
  (D : GeometricLemmaIntersectionDatum p l r hp hr hl hmul q lQ rQ hq hrQ hlQ hmulQ z)
  {A : CommGroupScheme (Spec (CommRingCat.of k))} {a : A.toGrp ⟶ L}

/-- For a datum with full source and full target parabolics, an exponent `χ` of `A_L` on the
piece at `σ` takes at `t` the scalar `s` by which the transported point
`(a ≫ (lQ' ≫ q')⁻¹ ≫ φ ≫ l' ≫ p')(t)` of `M(F)` acts on `σ`. The Jacquet module of `σ`
along `P'` must be admissible. -/
theorem piece_exponent_apply_eq_of_isIso [IsIso D.p'] [IsIso (D.lQ' ≫ D.q')]
    (ha : IsSplitComponent a) :
    haveI := hl.isConnectedReductive.isAffineHom
    letI := leviPointTopology l hl
    haveI := leviPoints_locallyCompactSpace p l hp hl
    haveI := leviPoints_nonarchimedeanGroup p l hp hl
    letI := leviPointTopology D.l' D.hl'
    ∀ σ : SmoothRep.{0, u, v} ℂ (rationalPoints M),
      ((leviJacquetFunctor D.p' D.l' D.r' D.hp' D.hr' D.hl' D.hmul').obj σ).IsAdmissible →
      ∀ χ : rationalPoints A.toGrp →* ℂˣ,
        IsGeneralizedEigencharacter ((D.pieceFunctor.obj σ).ρ.comp (rationalPoints.map a)) χ →
        ∀ (t : rationalPoints A.toGrp) (s : ℂ),
          (∀ v : σ, σ.representation (rationalPoints.map
            (a ≫ inv (D.lQ' ≫ D.q') ≫ D.φ.hom ≫ D.l' ≫ D.p') t) v = s • v) →
          (χ t : ℂ) = s := by
  have := hl.isConnectedReductive.isAffineHom
  let := leviPointTopology l hl
  have := leviPoints_locallyCompactSpace p l hp hl
  have := leviPoints_nonarchimedeanGroup p l hp hl
  let := leviPointTopology D.l' D.hl'
  intro σ hσ χ hχ t s hs
  have ha' : IsSplitComponent (a ≫ inv (D.lQ' ≫ D.q')) :=
    ha.comp_iso (asIso (D.lQ' ≫ D.q')).symm
  have hid : CommGroupScheme.groupHom (𝟙 A) = 𝟙 A.toGrp := rfl
  have hf : CommGroupScheme.groupHom (𝟙 A) ≫ (a ≫ inv (D.lQ' ≫ D.q')) ≫ D.lQ' ≫ D.q' = a := by
    rw [hid]
    simp
  obtain ⟨ψ, hψ, hψχ⟩ := D.exists_isNormalizedJacquetExponent_of_piece ha ha' (𝟙 A) hf σ hσ χ hχ
  have : IsIso D.l' := D.hl'.isIso_of_isIso_parabolic (p := D.p') hl.isConnectedReductive
  have hψt := normalizedJacquetExponent_apply_eq_of_smul D.p' D.l' D.r' D.hp' D.hl' D.hr'
    D.hmul' (ha'.comp_iso D.φ) σ ψ hψ t
    (splitComponentPointsMap_mem_center_of_isIso D.p' D.l' (ha'.comp_iso D.φ) t) s
    (by
      intro v
      convert hs v using 3
      simp only [splitComponentPointsMap_val, rationalPoints.map_apply, Grp.comp_hom_hom,
        Category.assoc])
  have hψid : ψ.comp (rationalPoints.map (CommGroupScheme.groupHom (𝟙 A))) = ψ := by
    refine MonoidHom.ext fun t => ?_
    simp only [hid, MonoidHom.comp_apply, rationalPoints.map_apply, Grp.id_hom_hom,
      Category.comp_id]
  rw [← hψχ, hψid]
  exact hψt

end GeometricLemmaIntersectionDatum

end RepresentedParabolic

end Langlands.Aubert.General
