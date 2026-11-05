import Langlands.GroupScheme.Rational.TorusGeneratedEnvelopeBaseChange
import Langlands.GroupScheme.Rational.TorusGeneratedEnvelopeNormalityReduction
import Langlands.GroupScheme.Rational.TorusUnipotentLiftConjugacy
import Langlands.GroupScheme.Rational.TorusVectorLinearizationProof
import Langlands.GroupScheme.Rational.SplitSeriesBaseChange
import Langlands.GroupScheme.SplitUnipotentAffineTorsorProof

/-! # Envelope normality from conjugates of a section of a unipotent quotient -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

section SectionLift

variable {S : Scheme.{u}} {G Q A : GroupScheme S}

/-- The lift of a homomorphism through a chosen section of its quotient. -/
def torusSectionLift (q : G ⟶ Q) (s : Q ⟶ G) (i : A ⟶ G) : A ⟶ G :=
  (i ≫ q) ≫ s

/-- The section lift has exactly the original quotient homomorphism. -/
theorem torusSectionLift_comp (q : G ⟶ Q) (s : Q ⟶ G)
    (hs : s ≫ q = 𝟙 Q) (i : A ⟶ G) :
    torusSectionLift q s i ≫ q = i ≫ q := by
  simp only [torusSectionLift, Category.assoc, hs, Category.comp_id]

end SectionLift

section BaseChangeConjugates

variable {S S' : Scheme.{u}} {G Q : GroupScheme S} (s : Q ⟶ G)
    {F : SubgroupFunctor G}

/-- Universal containment of conjugates of a specified subgroup is preserved
by arbitrary base change, with the same all-test meaning. -/
theorem conjugatesInto_baseChange (b : S' ⟶ S)
    (h : ∀ (R : Over S) (g x : R ⟶ G.X),
      x ∈ (SubgroupFunctor.range s).carrier R → g * x * g⁻¹ ∈ F.carrier R)
    (R : Over S') (g x : R ⟶ ((GroupScheme.baseChange b).obj G).X)
    (hx : x ∈ (SubgroupFunctor.range ((GroupScheme.baseChange b).map s)).carrier R) :
    g * x * g⁻¹ ∈ (F.baseChange b).carrier R := by
  rw [SubgroupFunctor.mem_baseChange, map_mul, map_mul, map_inv]
  apply h
  rw [SubgroupFunctor.range_baseChangeHom, SubgroupFunctor.mem_baseChange] at hx
  exact hx

end BaseChangeConjugates

namespace TorusGeneratedEnvelope

variable {k : Type u} [Field k]
    {G N Q : GroupScheme (Spec (CommRingCat.of k))}
    [Smooth G.X.hom] [IsAffineHom G.X.hom]
    (D : TorusGeneratedEnvelope G)

/-- A section of a represented split-unipotent quotient suffices for geometric
envelope compatibility, once all ambient conjugates of that section are in
the ground-field envelope. The stable-vector theorem remains explicit. -/
theorem algebraicClosure_envelope_eq_of_section_conjugates
    (hstable : RelativeRoot.SplitUnipotentStableVectorSubgroupStatement.{u})
    (n : N ⟶ G) (hn : IsClosedSubgroup n)
    [Smooth N.X.hom] [IsAffineHom N.X.hom] [ConnectedSpace N.X.left]
    (hN : IsUnipotent N) (hNsplit : RelativeRoot.IsSplitUnipotent N)
    (q : G ⟶ Q) (hq : RelativeRoot.IsFppfQuotient (SubgroupFunctor.range n) q)
    (s : Q ⟶ G) (hs : s ≫ q = 𝟙 Q)
    (htr : ∀ (R : Over (Spec (CommRingCat.of k))) (g x : R ⟶ G.X),
      x ∈ (SubgroupFunctor.range s).carrier R →
        g * x * g⁻¹ ∈ (closedTorusEnvelope G).carrier R) :
    (closedTorusEnvelope G).baseChange (toAlgebraicClosure k) =
      closedTorusEnvelope ((GroupScheme.baseChange (toAlgebraicClosure k)).obj G) := by
  let K := AlgebraicClosure k
  let b := toAlgebraicClosure k
  let bc := GroupScheme.baseChange b
  have : IsAffineHom (bc.obj G).X.hom :=
    inferInstanceAs (IsAffineHom (pullback.snd G.X.hom b))
  have : Smooth (bc.obj N).X.hom :=
    inferInstanceAs (Smooth (pullback.snd N.X.hom b))
  have : IsAffineHom (bc.obj N).X.hom :=
    inferInstanceAs (IsAffineHom (pullback.snd N.X.hom b))
  have : ConnectedSpace (bc.obj N).X.left :=
    N.connectedSpace_baseChange_of_smooth_affine b
  have hqb : RelativeRoot.IsFppfQuotient
      (SubgroupFunctor.range (bc.map n)) (bc.map q) := by
    rw [SubgroupFunctor.range_baseChangeHom]
    exact hq.baseChange b
  have hsb : bc.map s ≫ bc.map q = 𝟙 (bc.obj Q) := by
    rw [← bc.map_comp, hs]
    exact bc.map_id Q
  apply (closedTorusEnvelope_baseChange_eq_iff_containsTori K G).mpr
  intro A i hA _hi R x hx
  let i₀ := torusSectionLift (bc.map q) (bc.map s) i
  have hi₀ : i₀ ≫ bc.map q = i ≫ bc.map q :=
    torusSectionLift_comp _ _ hsb i
  have hconj := homConjugate_of_isTorus_fppf_split_unipotent_kernel_of_structuralStatements
    hstable RelativeRoot.torusVectorActionLinearization splitUnipotentAffineTorsorStatement
    (bc.map n) (hn.baseChange b) inferInstance inferInstance
    (hN.baseChange (K := K)) (hNsplit.baseChange K) (bc.map q) hqb i₀ i hi₀ hA
  obtain ⟨g, hg⟩ := (homConjugate_iff_points i₀ i).mp hconj
  obtain ⟨y, rfl⟩ := SubgroupFunctor.mem_range.mp hx
  rw [← hg R y]
  apply conjugatesInto_baseChange s b htr
  refine SubgroupFunctor.mem_range.mpr ⟨y ≫ (i ≫ bc.map q).hom.hom, ?_⟩
  change (y ≫ (i ≫ bc.map q).hom.hom) ≫ (bc.map s).hom.hom = y ≫ i₀.hom.hom
  simp only [i₀, torusSectionLift, Grp.comp_hom_hom, Category.assoc]

/-- Under the same section-conjugate containment, full normality follows by
geometric normality and fpqc descent. This preserves nonreduced test schemes. -/
theorem isNormal_of_section_conjugates
    (hstable : RelativeRoot.SplitUnipotentStableVectorSubgroupStatement.{u})
    (n : N ⟶ G) (hn : IsClosedSubgroup n)
    [Smooth N.X.hom] [IsAffineHom N.X.hom] [ConnectedSpace N.X.left]
    (hN : IsUnipotent N) (hNsplit : RelativeRoot.IsSplitUnipotent N)
    (q : G ⟶ Q) (hq : RelativeRoot.IsFppfQuotient (SubgroupFunctor.range n) q)
    (s : Q ⟶ G) (hs : s ≫ q = 𝟙 Q)
    (htr : ∀ (R : Over (Spec (CommRingCat.of k))) (g x : R ⟶ G.X),
      x ∈ (SubgroupFunctor.range s).carrier R →
        g * x * g⁻¹ ∈ (closedTorusEnvelope G).carrier R) :
    (SubgroupFunctor.range D.inclusion).IsNormal := by
  apply D.isNormal_of_algebraicClosure_envelope_eq
  exact algebraicClosure_envelope_eq_of_section_conjugates
    hstable n hn hN hNsplit q hq s hs htr

end TorusGeneratedEnvelope

end Langlands.GroupScheme
