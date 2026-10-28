import Langlands.Geometry.Analytic.StrictTestDomain.InvariantRationalSite
import Mathlib.CategoryTheory.Sites.CoverPreserving

/-! # Conjugation of finite invariant rational sites -/

noncomputable section

universe u v w w'

namespace Langlands.Analytic.StrictTestDomain.RationalAutomorphism.RationalSpectralAction

open CategoryTheory

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {P : PresentedStrictAffinoidAlgebra K}
  {G : Type v} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  (ρ : RationalSpectralAction G P)

/-- The actual open subgroup gUg⁻¹, obtained by continuous inverse conjugation. -/
def conjugateOpenSubgroup (U : OpenSubgroup G) (g : G) : OpenSubgroup G :=
  U.comap (MulAut.conj g⁻¹).toMonoidHom (IsTopologicalGroup.continuous_conj g⁻¹)

@[simp]
theorem mem_conjugateOpenSubgroup (U : OpenSubgroup G) (g k : G) :
    k ∈ conjugateOpenSubgroup U g ↔ g⁻¹ * k * g ∈ U := by
  change g⁻¹ * k * (g⁻¹)⁻¹ ∈ U ↔ g⁻¹ * k * g ∈ U
  rw [inv_inv]

/-- Inverse conjugation recovers the original open subgroup exactly. -/
@[simp]
theorem conjugateOpenSubgroup_inv (U : OpenSubgroup G) (g : G) :
    conjugateOpenSubgroup (conjugateOpenSubgroup U g) g⁻¹ = U := by
  ext k
  simp [mul_assoc]

/-- The published stabilizer conjugation law pulled back to the acting group. -/
theorem mem_locusOpenSubgroup_smul_iff (g k : G) (d : RationalData K P) :
    k ∈ ρ.locusOpenSubgroup (ρ.toMonoidHom g • d) ↔
      g⁻¹ * k * g ∈ ρ.locusOpenSubgroup d := by
  change ρ.toMonoidHom k ∈ locusStabilizer (ρ.toMonoidHom g • d) ↔
    ρ.toMonoidHom (g⁻¹ * k * g) ∈ locusStabilizer d
  simpa [map_mul, map_inv, mul_assoc] using
    (conj_mem_locusStabilizer_iff (ρ.toMonoidHom g)
      (ρ.toMonoidHom (g⁻¹ * k * g)) d)

/-- The moved actual rational locus has the conjugate open stabilizer. -/
theorem locusOpenSubgroup_smul (g : G) (d : RationalData K P) :
    ρ.locusOpenSubgroup (ρ.toMonoidHom g • d) =
      conjugateOpenSubgroup (ρ.locusOpenSubgroup d) g := by
  ext k
  rw [mem_conjugateOpenSubgroup]
  exact ρ.mem_locusOpenSubgroup_smul_iff g k d

/-- Transport actual rational presentations and their inclusions; the target
subgroup may be any open subgroup of gUg⁻¹. -/
def invariantTransportFunctor (g : G) {U V : OpenSubgroup G}
    (h : V ≤ conjugateOpenSubgroup U g) :
    ρ.InvariantRationalDomain U ⥤ ρ.InvariantRationalDomain V :=
  (ρ.invariantRationalProperty V).lift
    ((ρ.invariantRationalProperty U).ι ⋙ actionFunctor (ρ.toMonoidHom g))
    (fun d k hk => (ρ.mem_locusOpenSubgroup_smul_iff g k d.obj).mpr
      (d.property ((mem_conjugateOpenSubgroup U g k).mp (h hk))))

@[simp]
theorem invariantTransportFunctor_obj_obj (g : G) {U V : OpenSubgroup G}
    (h : V ≤ conjugateOpenSubgroup U g) (d : ρ.InvariantRationalDomain U) :
    ((ρ.invariantTransportFunctor g h).obj d).obj = ρ.toMonoidHom g • d.obj :=
  rfl

/-- Forgetting invariance recovers exactly the published rational action functor. -/
@[simp]
theorem invariantTransportFunctor_forget (g : G) {U V : OpenSubgroup G}
    (h : V ≤ conjugateOpenSubgroup U g) :
    ρ.invariantTransportFunctor g h ⋙ (ρ.invariantRationalProperty V).ι =
      (ρ.invariantRationalProperty U).ι ⋙ actionFunctor (ρ.toMonoidHom g) :=
  rfl

/-- The actual bounded quotient comparisons commute with transported restriction. -/
theorem invariantTransport_restriction (g : G) {U V : OpenSubgroup G}
    (h : V ≤ conjugateOpenSubgroup U g) {d e : ρ.InvariantRationalDomain U}
    (f : d ⟶ e) (a : e.obj.algebra) :
    ((ρ.invariantTransportFunctor g h).map f).hom.restriction
        (e.obj.comparison (ρ.toMonoidHom g).hom a) =
      d.obj.comparison (ρ.toMonoidHom g).hom (f.hom.restriction a) :=
  restriction_transport f.hom (ρ.toMonoidHom g) a

private theorem conjugation_hom_unique {U : OpenSubgroup G}
    {d e : ρ.InvariantRationalDomain U} (f k : d ⟶ e) : f = k := by
  apply ObjectProperty.hom_ext
  exact (inferInstance : Subsingleton (RationalData.Inclusion d.obj e.obj)).elim _ _

/-- Conjugation is an equivalence on actual invariant rational presentations.
The inverse applies g⁻¹ to the chosen rational data. -/
def invariantConjugationEquivalence (U : OpenSubgroup G) (g : G) :
    ρ.InvariantRationalDomain U ≌
      ρ.InvariantRationalDomain (conjugateOpenSubgroup U g) where
  functor := ρ.invariantTransportFunctor g (le_refl _)
  inverse := ρ.invariantTransportFunctor g⁻¹
    (le_of_eq (conjugateOpenSubgroup_inv U g).symm)
  unitIso := NatIso.ofComponents (fun d => (ρ.invariantRationalProperty U).isoMk (eqToIso (by
    change d.obj = ρ.toMonoidHom g⁻¹ • (ρ.toMonoidHom g • d.obj)
    rw [map_inv, inv_smul_smul]))) (fun _ => conjugation_hom_unique ρ _ _)
  counitIso := NatIso.ofComponents (fun d => (ρ.invariantRationalProperty (conjugateOpenSubgroup U g)).isoMk (eqToIso (by
    change ρ.toMonoidHom g • (ρ.toMonoidHom g⁻¹ • d.obj) = d.obj
    rw [map_inv, smul_inv_smul]))) (fun _ => conjugation_hom_unique ρ _ _)
  functor_unitIso_comp _ := conjugation_hom_unique ρ _ _

/-- The same finite family covers after moving every actual locus. -/
theorem invariantTransport_isFiniteCovering_pushforward (g : G)
    {U V : OpenSubgroup G} (h : V ≤ conjugateOpenSubgroup U g)
    {d : ρ.InvariantRationalDomain U} {S : Sieve d}
    (hS : InvariantRationalDomain.IsFiniteCovering ρ U S) :
    InvariantRationalDomain.IsFiniteCovering ρ V
      (S.functorPushforward (ρ.invariantTransportFunctor g h)) := by
  obtain ⟨I, hI, D, f, hf, hcover⟩ := hS
  refine ⟨I, hI, fun i => (ρ.invariantTransportFunctor g h).obj (D i),
    fun i => (ρ.invariantTransportFunctor g h).map (f i), ?_, ?_⟩
  · intro i
    exact Sieve.image_mem_functorPushforward (ρ.invariantTransportFunctor g h) S (hf i)
  · exact (familyCovers_smul_iff (ρ.toMonoidHom g) d.obj
      (fun i => (D i).obj)).mpr hcover

/-- A covering image sieve factors through finitely many transported original
arrows. Applying the inverse point action shows their original loci cover. -/
theorem invariantTransport_isFiniteCovering_of_pushforward (g : G)
    {U V : OpenSubgroup G} (h : V ≤ conjugateOpenSubgroup U g)
    {d : ρ.InvariantRationalDomain U} {S : Sieve d}
    (hS : InvariantRationalDomain.IsFiniteCovering ρ V
      (S.functorPushforward (ρ.invariantTransportFunctor g h))) :
    InvariantRationalDomain.IsFiniteCovering ρ U S := by
  classical
  obtain ⟨I, hI, E, f, hf, hcover⟩ := hS
  choose D k a hk _ using hf
  refine ⟨I, hI, D, k, hk, ?_⟩
  intro x hx
  obtain ⟨i, hi⟩ := hcover (ρ.toMonoidHom g • x)
    ((smul_mem_smul_locus_iff (ρ.toMonoidHom g) d.obj x).mpr hx)
  exact ⟨i, (smul_mem_smul_locus_iff (ρ.toMonoidHom g) (D i).obj x).mp
    ((a i).hom.subset hi)⟩

/-- Transport preserves and reflects finite covering of an arbitrary sieve. -/
theorem invariantTransport_pushforward_mem_iff (g : G)
    {U V : OpenSubgroup G} (h : V ≤ conjugateOpenSubgroup U g)
    {d : ρ.InvariantRationalDomain U} (S : Sieve d) :
    S.functorPushforward (ρ.invariantTransportFunctor g h) ∈
        InvariantRationalDomain.finiteRationalTopology ρ V
          ((ρ.invariantTransportFunctor g h).obj d) ↔
      S ∈ InvariantRationalDomain.finiteRationalTopology ρ U d :=
  ⟨ρ.invariantTransport_isFiniteCovering_of_pushforward g h,
    ρ.invariantTransport_isFiniteCovering_pushforward g h⟩

/-- Conjugation, also with a smaller target subgroup, preserves finite covers. -/
theorem invariantTransport_coverPreserving (g : G)
    {U V : OpenSubgroup G} (h : V ≤ conjugateOpenSubgroup U g) :
    CoverPreserving (InvariantRationalDomain.finiteRationalTopology ρ U)
      (InvariantRationalDomain.finiteRationalTopology ρ V)
      (ρ.invariantTransportFunctor g h) :=
  ⟨fun hS => ρ.invariantTransport_isFiniteCovering_pushforward g h hS⟩

/-- The forward category equivalence is compatible-preserving because every
comparison object is isomorphic to the image of its inverse transport. -/
theorem invariantConjugation_compatiblePreserving (U : OpenSubgroup G) (g : G) :
    CompatiblePreserving.{w}
      (InvariantRationalDomain.finiteRationalTopology ρ (conjugateOpenSubgroup U g))
      (ρ.invariantConjugationEquivalence U g).functor :=
  compatiblePreservingOfDownwardsClosed
    (InvariantRationalDomain.finiteRationalTopology ρ (conjugateOpenSubgroup U g))
    (ρ.invariantConjugationEquivalence U g).functor
    (fun {_ d} _ => ⟨(ρ.invariantConjugationEquivalence U g).inverse.obj d,
      (ρ.invariantConjugationEquivalence U g).counitIso.app d⟩)

/-- Conjugation is continuous for the actual finite invariant rational sites. -/
instance invariantConjugation_isContinuous (U : OpenSubgroup G) (g : G) :
    (ρ.invariantConjugationEquivalence U g).functor.IsContinuous
      (InvariantRationalDomain.finiteRationalTopology ρ U)
      (InvariantRationalDomain.finiteRationalTopology ρ (conjugateOpenSubgroup U g)) :=
  Functor.isContinuous_of_coverPreserving
    (ρ.invariantConjugation_compatiblePreserving U g)
    (ρ.invariantTransport_coverPreserving g (U := U) (le_refl _))

/-- The inverse equivalence has the same compatibility property. -/
theorem invariantConjugationInverse_compatiblePreserving (U : OpenSubgroup G) (g : G) :
    CompatiblePreserving.{w} (InvariantRationalDomain.finiteRationalTopology ρ U)
      (ρ.invariantConjugationEquivalence U g).inverse :=
  compatiblePreservingOfDownwardsClosed
    (InvariantRationalDomain.finiteRationalTopology ρ U)
    (ρ.invariantConjugationEquivalence U g).inverse
    (fun {_ d} _ => ⟨(ρ.invariantConjugationEquivalence U g).functor.obj d,
      (ρ.invariantConjugationEquivalence U g).unitIso.symm.app d⟩)

/-- Inverse conjugation is continuous for the finite invariant rational sites. -/
instance invariantConjugationInverse_isContinuous (U : OpenSubgroup G) (g : G) :
    (ρ.invariantConjugationEquivalence U g).inverse.IsContinuous
      (InvariantRationalDomain.finiteRationalTopology ρ (conjugateOpenSubgroup U g))
      (InvariantRationalDomain.finiteRationalTopology ρ U) :=
  Functor.isContinuous_of_coverPreserving
    (ρ.invariantConjugationInverse_compatiblePreserving U g)
    (ρ.invariantTransport_coverPreserving g⁻¹
      (le_of_eq (conjugateOpenSubgroup_inv U g).symm))

/-- Precomposition with actual conjugation transports categorical sheaves. -/
def invariantSheafConjugation (U : OpenSubgroup G) (g : G)
    (A : Type w) [Category.{w'} A] :
    Sheaf (InvariantRationalDomain.finiteRationalTopology ρ (conjugateOpenSubgroup U g)) A ⥤
      Sheaf (InvariantRationalDomain.finiteRationalTopology ρ U) A :=
  (ρ.invariantConjugationEquivalence U g).functor.sheafPushforwardContinuous A
    (InvariantRationalDomain.finiteRationalTopology ρ U)
    (InvariantRationalDomain.finiteRationalTopology ρ (conjugateOpenSubgroup U g))

/-- Its underlying presheaf is exactly precomposition by the transported domain functor. -/
theorem invariantSheafConjugation_obj (U : OpenSubgroup G) (g : G)
    (A : Type w) [Category.{w'} A]
    (F : Sheaf (InvariantRationalDomain.finiteRationalTopology ρ
      (conjugateOpenSubgroup U g)) A) :
    ((ρ.invariantSheafConjugation U g A).obj F).obj =
      (ρ.invariantConjugationEquivalence U g).functor.op ⋙ F.obj :=
  rfl

end Langlands.Analytic.StrictTestDomain.RationalAutomorphism.RationalSpectralAction
