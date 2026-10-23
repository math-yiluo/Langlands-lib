import Langlands.Geometry.Analytic.StrictTestDomain.RationalTransportCovering

/-! # Restriction from the finite rational transport site -/

noncomputable section

universe u v w

namespace Langlands.Analytic.StrictTestDomain.RationalTransport

open CategoryTheory

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {P : PresentedStrictAffinoidAlgebra K}

/-- Transport maps with a common label lift to the actual rational intersection. -/
def inclusionInterLift {X : RationalTransport K P} {d e : RationalData K P}
    (f : X ⟶ inclusion.obj d) (g : X ⟶ inclusion.obj e)
    (h : f.label = g.label) : X ⟶ inclusion.obj (d.inter e) :=
  ⟨f.label, by
    intro x hx
    change f.label • x ∈ (d.inter e).locus
    rw [RationalData.locus_inter]
    exact ⟨f.mapsTo x hx, h ▸ g.mapsTo x hx⟩⟩

@[simp] theorem inclusionInterLift_left {X : RationalTransport K P}
    {d e : RationalData K P} (f : X ⟶ inclusion.obj d) (g : X ⟶ inclusion.obj e)
    (h : f.label = g.label) :
    inclusionInterLift f g h ≫ inclusion.map (RationalData.interLeft d e) = f := by
  apply Hom.ext
  exact one_mul _

@[simp] theorem inclusionInterLift_right {X : RationalTransport K P}
    {d e : RationalData K P} (f : X ⟶ inclusion.obj d) (g : X ⟶ inclusion.obj e)
    (h : f.label = g.label) :
    inclusionInterLift f g h ≫ inclusion.map (RationalData.interRight d e) = g := by
  apply Hom.ext
  exact (one_mul _).trans h

omit [CompleteSpace K] in
/-- Equality after ordinary inclusions forces the retained transport labels
to agree. -/
theorem label_eq_of_comp_inclusion_eq {X : RationalTransport K P}
    {d e t : RationalData K P} (f : X ⟶ inclusion.obj d) (g : X ⟶ inclusion.obj e)
    (a : d ⟶ t) (b : e ⟶ t) (h : f ≫ inclusion.map a = g ≫ inclusion.map b) :
    f.label = g.label := by
  have h' := congrArg Hom.label h
  change 1 * f.label = 1 * g.label at h'
  simpa only [one_mul] using h'

/-- The common-label lift transfers compatibility from ordinary inclusions
to all transport comparisons. -/
theorem inclusion_compatiblePreserving :
    CompatiblePreserving.{w} (finiteTopology K P) inclusion := by
  constructor
  intro ℱ Z T x hx Y₁ Y₂ X f₁ f₂ g₁ g₂ hg₁ hg₂ heq
  let l := inclusionInterLift f₁ f₂
    (label_eq_of_comp_inclusion_eq f₁ f₂ g₁ g₂ heq)
  have h := hx (RationalData.interLeft Y₁ Y₂) (RationalData.interRight Y₁ Y₂)
    hg₁ hg₂ ((inferInstance :
      Subsingleton (RationalData.Inclusion (Y₁.inter Y₂) Z)).elim _ _)
  have h' := congrArg (ℱ.obj.map l.op) h
  have e₁ : l ≫ inclusion.map (RationalData.interLeft Y₁ Y₂) = f₁ :=
    inclusionInterLift_left _ _ _
  have e₂ : l ≫ inclusion.map (RationalData.interRight Y₁ Y₂) = f₂ :=
    inclusionInterLift_right _ _ _
  rw [← e₁, ← e₂, op_comp, op_comp, ℱ.obj.map_comp, ℱ.obj.map_comp]
  exact h'

/-- The ordinary rational inclusion is continuous for the constructed finite
covering topologies. -/
instance inclusion_isContinuous :
    (inclusion (K := K) (P := P)).IsContinuous
      (RationalData.finiteRationalTopology K P) (finiteTopology K P) :=
  Functor.isContinuous_of_coverPreserving inclusion_compatiblePreserving
    inclusion_coverPreserving

/-- Restrict a transport-site sheaf to ordinary rational inclusions,
with arbitrary categorical coefficients. -/
def rationalSheafRestriction (A : Type v) [Category.{w} A] :
    Sheaf (finiteTopology K P) A ⥤ Sheaf (RationalData.finiteRationalTopology K P) A :=
  inclusion.sheafPushforwardContinuous A
    (RationalData.finiteRationalTopology K P) (finiteTopology K P)

/-- The restricted bounded presheaf is the published actual rational quotient
presheaf; the components are identities on the same quotient algebras. -/
def inclusionBoundedPresheafIso :
    (inclusion (K := K) (P := P)).op ⋙ boundedPresheaf ≅
      RationalData.rationalBoundedPresheaf K P :=
  NatIso.ofComponents (fun _ => Iso.refl _) (by
    intro X Y f
    change (BoundedAlgHom.id K Y.unop.algebra).comp
        (inclusion.map f.unop).restriction =
      f.unop.restriction.comp (BoundedAlgHom.id K X.unop.algebra)
    rw [inclusion_restriction]
    rfl)

/-- The same identity comparison after forgetting to commutative algebras. -/
def inclusionAlgebraPresheafIso :
    (inclusion (K := K) (P := P)).op ⋙ algebraPresheaf ≅
      RationalData.rationalPresheaf K P :=
  (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight inclusionBoundedPresheafIso
      (PresentedStrictAffinoidAlgebra.toCommAlgCat K)

/-- Any sheaf proof for the actual transport algebra presheaf restricts to a
sheaf proof for the actual rational quotient presheaf. -/
theorem rationalPresheaf_isSheaf_of_transport
    (h : Presheaf.IsSheaf (finiteTopology K P) algebraPresheaf) :
    Presheaf.IsSheaf (RationalData.finiteRationalTopology K P)
      (RationalData.rationalPresheaf K P) :=
  (Presheaf.isSheaf_of_iso_iff inclusionAlgebraPresheafIso).mp
    (inclusion.op_comp_isSheaf_of_isSheaf
      (RationalData.finiteRationalTopology K P) (finiteTopology K P) _ h)

end Langlands.Analytic.StrictTestDomain.RationalTransport
