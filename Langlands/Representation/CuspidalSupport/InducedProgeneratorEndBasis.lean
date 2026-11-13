import Langlands.Representation.CuspidalSupport.InducedProgeneratorEndFreeStatement
import Langlands.Representation.CuspidalSupport.NormKernelSummandPullback
import Langlands.Representation.CuspidalSupport.LeviCenterDescent
import Langlands.Representation.Filtration.InducedEndBasis
import Langlands.Representation.Exponents.ActualGeometricFullPieceNaturality
import Langlands.Representation.Exponents.LeviJacquetInductionSupercuspidalFiltrationProof
import Langlands.Representation.Geometric.RepresentedGeometricLemmaProof
import Langlands.Representation.Geometric.RepresentedGeometricLemmaGeometryProof
import Langlands.Representation.Geometric.ClosedSubgroupOrbitOrdering
import Langlands.GroupScheme.Rational.ParabolicLeviTorusConjugation
import Langlands.GroupScheme.Rational.MaximalLeviDynamicReduction
import Langlands.Geometry.Building.ValuationBuildingIsoTransport
import Langlands.Representation.CuspidalSupport.NormalizerDoubleCosets

/-! # A basis of the endomorphisms of the induced progenerator -/

noncomputable section

universe u v

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.SmoothRep

universe uR uG uV

variable {R : Type uR} [CommRing R] {Γ : Type uG} [Group Γ] [TopologicalSpace Γ]

/-- A surjection from a smooth representation onto a representation isomorphic to a
projective smooth representation has a section. -/
theorem exists_section_of_projective {Z Y : Rep.{uV} R Γ} (hZ : IsSmooth Z.ρ)
    (f : Z ⟶ Y) (hf : Function.Surjective f.hom) (P : SmoothRep.{uR, uG, uV} R Γ)
    [Projective P] (iY : Y ≅ toRep.obj P) : ∃ σ : Y ⟶ Z, σ ≫ f = 𝟙 Y := by
  let Zs : SmoothRep.{uR, uG, uV} R Γ := ⟨Z, hZ⟩
  let f' : Zs ⟶ P := toRep.preimage (f ≫ iY.hom)
  have hf' : toRep.map f' = f ≫ iY.hom := toRep.map_preimage _
  have : Epi f' := by
    rw [epi_iff_surjective]
    intro y
    obtain ⟨x, hx⟩ := hf (iY.inv.hom y)
    refine ⟨x, ?_⟩
    have h := congrArg (fun g => g.hom x) hf'
    change (toRep.map f').hom x = _
    rw [h]
    change iY.hom.hom (f.hom x) = y
    rw [hx]
    exact congrArg (fun g => g.hom y) iY.inv_hom_id
  let g := Projective.factorThru (𝟙 P) f'
  have hg : toRep.map g ≫ f ≫ iY.hom = 𝟙 _ := by
    rw [← hf', ← Functor.map_comp, Projective.factorThru_comp, CategoryTheory.Functor.map_id]
  refine ⟨iY.hom ≫ toRep.map g, ?_⟩
  calc (iY.hom ≫ toRep.map g) ≫ f = iY.hom ≫ (toRep.map g ≫ f ≫ iY.hom) ≫ iY.inv := by
        simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]
    _ = 𝟙 Y := by rw [hg, Category.id_comp, Iso.hom_inv_id]

end Langlands.SmoothRep

namespace Langlands.RepFunctorFiltration

universe uR uG uV uC vC uD vD

/-- `inducedEndBasis` for a filtration of a functor `Φ` equal to `Ind ⋙ Res ⋙ T`. The
filtration fixes `Φ` and the equation comes last, so the hypotheses are checked against `Φ`
itself rather than against the composite read off the adjunction. -/
theorem nonempty_inducedEndBasis_of_comp_eq {R : Type uR} {G : Type uG} [CommRing R]
    [Monoid G] {C : Type uC} [Category.{vC} C] [Preadditive C] {D : Type uD}
    [Category.{vD} D] [Preadditive D] {Ind : C ⥤ D} {Res : D ⥤ C} (adj : Res ⊣ Ind)
    [Ind.Additive] [Res.Additive] (T : C ⥤ Rep.{uV} R G) [T.Additive] [T.Full] [T.Faithful]
    {Φ : C ⥤ Rep.{uV} R G} {n : ℕ} (s : RepFunctorFiltration Φ n) (X : C)
    (hsec : ∀ k : Fin n, ∃ σ : (s.graded k).obj X ⟶ (s.step k.succ).representation X,
      σ ≫ s.gradedProjection X k = 𝟙 _)
    (θ : ∀ j : Fin n, (s.graded j).obj X ⟶ T.obj X) (S : Finset (Fin n))
    (hθ : ∀ j ∈ S, Function.Bijective (fun a : X ⟶ X => (s.graded j).map a ≫ θ j))
    (hzero : ∀ j ∉ S, ∀ g : (s.graded j).obj X ⟶ T.obj X, g = 0)
    (hΦ : Ind ⋙ Res ⋙ T = Φ) :
    letI := endPrecompModule Ind X (Ind.obj X)
    Nonempty (Module.Basis S (End X)ᵐᵒᵖ (Ind.obj X ⟶ Ind.obj X)) := by
  subst hΦ
  exact ⟨inducedEndBasis adj T s X hsec θ S hθ hzero⟩

/-- A basis of `Φ X ⟶ Z` over `(End X)ᵐᵒᵖ`, acting by precomposition with `Φ.map`, indexed by
a type `J ≃ Fin m`, gives maps `b₁, …, b_m` such that every `x : Φ X ⟶ Z` is uniquely
`∑ Φ.map (aᵢ) ≫ bᵢ`. -/
theorem existsUnique_precomp_expansion_of_basis {C : Type uC} [Category.{vC} C] [Preadditive C]
    {D : Type uD} [Category.{vD} D] [Preadditive D] (Φ : C ⥤ D) [Φ.Additive] (X : C) (Z : D)
    {J : Type*} {m : ℕ} (e : J ≃ Fin m)
    (B : letI := endPrecompModule Φ X Z; Module.Basis J (End X)ᵐᵒᵖ (Φ.obj X ⟶ Z)) :
    ∃ b : Fin m → (Φ.obj X ⟶ Z), ∀ x : Φ.obj X ⟶ Z,
      ∃! a : Fin m → (X ⟶ X), x = ∑ i, Φ.map (a i) ≫ b i := by
  let _ := endPrecompModule Φ X Z
  let b := B.reindex e
  have hsum : ∀ c : Fin m → (End X)ᵐᵒᵖ, b.equivFun.symm c = ∑ j, Φ.map (c j).unop ≫ b j :=
    fun c => b.equivFun_symm_apply c
  refine ⟨b, fun x => ⟨fun j => (b.equivFun x j).unop, ?_, fun a ha => ?_⟩⟩
  · change x = ∑ j, Φ.map (MulOpposite.op (b.equivFun x j).unop).unop ≫ b j
    simp only [MulOpposite.op_unop]
    rw [← hsum, LinearEquiv.symm_apply_apply]
  · funext j
    have h : b.equivFun.symm (fun j => MulOpposite.op (a j)) = x := by
      rw [hsum]
      exact ha.symm
    rw [← h, LinearEquiv.apply_symm_apply]
    rfl

end Langlands.RepFunctorFiltration

namespace Langlands.Aubert.General.RepresentedParabolic

open GroupScheme

section Datum

variable {k : Type u} [Field k] [TopologicalSpace k] [T2Space k]
  {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]

local instance inducedProgeneratorBasisAmbientTopology : TopologicalSpace (rationalPoints G) :=
  RationalPointFamily.pointTopology

variable [LocallyCompactSpace (rationalPoints G)] [NonarchimedeanGroup (rationalPoints G)]
  {P M N : GroupScheme (Spec (CommRingCat.of k))}
  {p : P ⟶ G} {l : M ⟶ P} {r : N ⟶ P} {hp : IsParabolicSubgroup p}
  {hr : LeviSubgroup.IsGeometricUnipotentRadical r} {hl : IsRationalLeviSubgroup l}
  {hmul : IsIso (subgroupMultiplication l r)} {z : rationalPoints G}

namespace GeometricLemmaIntersectionDatum

variable (D : GeometricLemmaIntersectionDatum p l r hp hr hl hmul p l r hp hr hl hmul z)

omit [T2Space k] [IsAffineHom G.X.hom] [LocallyCompactSpace (rationalPoints G)]
  [NonarchimedeanGroup (rationalPoints G)] in
/-- If `z` normalizes `M`, through `φ : M ≅ M` with `φ ∘ (l ≫ p) = (l ≫ p) ∘ inn(z)`, then
the source intersection `M ∩ zPz⁻¹` of a self-intersection datum at `z` is all of `M`. -/
theorem isIso_p'_of_normalizes (φ : M ≅ M)
    (hφ : φ.hom ≫ l ≫ p = l ≫ p ≫ (G.innerIso z).hom) : IsIso D.p' := by
  have hj : IsClosedSubgroup (l ≫ p) := hl.isClosedSubgroup.comp hp.isClosedSubgroup
  have : IsClosedImmersion (l ≫ p).hom.hom.left := hj
  have : Mono (l ≫ p).hom.hom := Over.mono_of_mono_left _
  have hrange : SubgroupFunctor.range D.p' =
      (SubgroupFunctor.range (p ≫ (G.innerIso z).hom)).comap (l ≫ p) :=
    SubgroupFunctor.range_eq_comap_of_range_comp_eq_inf D.p' (l ≫ p)
      (SubgroupFunctor.range (p ≫ (G.innerIso z).hom)) (by
        simpa only [Category.assoc] using D.parabolic_eq)
  have hφ' : φ.inv ≫ l ≫ p ≫ (G.innerIso z).hom = l ≫ p := by
    rw [← hφ, Iso.inv_hom_id_assoc]
  have hfull : SubgroupFunctor.range D.p' = ⊤ := by
    rw [hrange]
    apply SubgroupFunctor.ext
    intro T
    apply Subgroup.ext
    intro x
    constructor
    · intro _
      trivial
    intro _
    apply SubgroupFunctor.mem_comap.mpr
    apply SubgroupFunctor.mem_range.mpr
    refine ⟨x ≫ φ.inv.hom.hom ≫ l.hom.hom, ?_⟩
    have heq := congrArg (fun f : M ⟶ G => f.hom.hom) hφ'
    simpa only [Grp.comp_hom_hom, Category.assoc] using congrArg (fun f => x ≫ f) heq
  have : IsClosedImmersion D.p'.hom.hom.left := D.hp'.isClosedSubgroup
  exact isIso_of_full_range D.p' (Over.mono_of_mono_left _) hfull

omit [T2Space k] [IsAffineHom G.X.hom] [LocallyCompactSpace (rationalPoints G)]
  [NonarchimedeanGroup (rationalPoints G)] in
/-- For a full self-intersection datum, the recovered conjugacy `M ≅ M` is the unique
`φ` with `φ ∘ (l ≫ p) = (l ≫ p) ∘ inn(z)`. -/
theorem fullTargetConjugacy_hom_eq [IsIso D.p'] (φ : M ≅ M)
    (hφ : φ.hom ≫ l ≫ p = l ≫ p ≫ (G.innerIso z).hom) :
    (D.fullTargetConjugacy (Iso.refl M) inferInstance).val.hom = φ.hom := by
  have hj : IsClosedSubgroup (l ≫ p) := hl.isClosedSubgroup.comp hp.isClosedSubgroup
  have : IsClosedImmersion (l ≫ p).hom.hom.left := hj
  have : Mono (l ≫ p).hom.hom := Over.mono_of_mono_left _
  have h := (D.fullTargetConjugacy (Iso.refl M) inferInstance).property
  apply Grp.hom_ext
  rw [← cancel_mono (l ≫ p).hom.hom, ← Grp.comp_hom_hom, ← Grp.comp_hom_hom, h, hφ]

end GeometricLemmaIntersectionDatum

end Datum

section Pieces

variable {k : Type u} [Field k] [ValuativeRel k] [TopologicalSpace k]
  [IsNonarchimedeanLocalField k] [T2Space k]
  {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]

local instance inducedProgeneratorPieceAmbientTopology : TopologicalSpace (rationalPoints G) :=
  RationalPointFamily.pointTopology

variable [LocallyCompactSpace (rationalPoints G)] [NonarchimedeanGroup (rationalPoints G)]
  {P M N : GroupScheme (Spec (CommRingCat.of k))}
  {p : P ⟶ G} {l : M ⟶ P} {r : N ⟶ P} {hp : IsParabolicSubgroup p}
  {hr : LeviSubgroup.IsGeometricUnipotentRadical r} {hl : IsRationalLeviSubgroup l}
  {hmul : IsIso (subgroupMultiplication l r)} {z : rationalPoints G}

namespace GeometricLemmaIntersectionDatum

variable (D : GeometricLemmaIntersectionDatum p l r hp hr hl hmul p l r hp hr hl hmul z)

omit [ValuativeRel k] [IsNonarchimedeanLocalField k] in
/-- A surjection from a smooth representation onto a representation isomorphic to the piece
of a projective supercuspidal `σ` at a self-intersection datum has a section: a full piece is a
pullback of `σ` along an automorphism of `M(F)`, hence projective, and the other pieces vanish. -/
theorem exists_section_of_iso_pieceFunctor_obj
    (σ : letI := leviPointTopology l hl; SmoothRep.{0, u, max u v} ℂ (rationalPoints M))
    (hproj : letI := leviPointTopology l hl; Projective σ)
    (hsc : haveI := hl.isConnectedReductive.isAffineHom
      letI := leviPointTopology l hl
      haveI := leviPoints_locallyCompactSpace p l hp hl
      haveI := leviPoints_nonarchimedeanGroup p l hp hl
      IsSupercuspidal σ)
    {Z Y : letI := leviPointTopology l hl; Rep.{max u v} ℂ (rationalPoints M)}
    (hZ : letI := leviPointTopology l hl; IsSmooth Z.ρ) (f : Z ⟶ Y)
    (hf : Function.Surjective f.hom) (iY : Y ≅ D.pieceFunctor.obj σ) :
    ∃ s : Y ⟶ Z, s ≫ f = 𝟙 Y := by
  have := hl.isConnectedReductive.isAffineHom
  let := leviPointTopology l hl
  have := leviPoints_locallyCompactSpace p l hp hl
  have := leviPoints_nonarchimedeanGroup p l hp hl
  by_cases h : IsIso D.p'
  · let eD := D.fullTargetPointsEquiv (Iso.refl M) h
    have : Projective (SmoothRep.pullback eD σ) :=
      ((SmoothRep.pullbackEquivalence eD).map_projective_iff σ).mpr hproj
    exact SmoothRep.exists_section_of_projective hZ f hf (SmoothRep.pullback eD σ)
      (iY ≪≫ Rep.mkIso (D.fullTargetPieceEquiv (Iso.refl M) h σ))
  · have : Subsingleton (D.pieceFunctor.obj σ) := D.subsingleton_pieceFunctor_obj σ
      (hsc _ _ _ D.p' D.l' D.r' D.hp' D.hl' D.hr' D.hmul' h)
    have hY : ∀ a b : Y, a = b := fun a b => by
      have ha : iY.inv.hom (iY.hom.hom a) = a := congrArg (fun g => g.hom a) iY.hom_inv_id
      have hb : iY.inv.hom (iY.hom.hom b) = b := congrArg (fun g => g.hom b) iY.hom_inv_id
      rw [← ha, ← hb, Subsingleton.elim (iY.hom.hom a) (iY.hom.hom b)]
    refine ⟨0, ?_⟩
    ext y
    exact hY _ _


omit [ValuativeRel k] [IsNonarchimedeanLocalField k] in
/-- At a full self-intersection datum, if the inducing representation `σ` is isomorphic to its
pullback along the recovered automorphism of `M(F)`, then precomposition with the piece functor's
maps, followed by one fixed map `θ`, is a bijection `End(σ) ≃ Hom(piece of σ, σ)`. -/
theorem exists_bijective_of_pullback_iso
    (σ : letI := leviPointTopology l hl; SmoothRep.{0, u, max u v} ℂ (rationalPoints M))
    (h : IsIso D.p')
    (ψ : letI := leviPointTopology l hl
      SmoothRep.pullback (D.fullTargetPointsEquiv (Iso.refl M) h) σ ≅ σ) :
    letI := leviPointTopology l hl
    ∃ θ : D.pieceFunctor.obj σ ⟶ SmoothRep.toRep.obj σ,
      Function.Bijective (fun a : σ ⟶ σ => D.pieceFunctor.map a ≫ θ) := by
  have := hl.isConnectedReductive.isAffineHom
  let := leviPointTopology l hl
  have := leviPoints_locallyCompactSpace p l hp hl
  have := leviPoints_nonarchimedeanGroup p l hp hl
  have := D.isIso_q'_of_isIso_p'_of_iso (Iso.refl M)
  let eD := D.fullTargetPointsEquiv (Iso.refl M) h
  let iD : D.pieceFunctor.obj σ ≅ SmoothRep.toRep.obj ((SmoothRep.pullbackFunctor eD).obj σ) :=
    Rep.mkIso (D.fullTargetPieceEquiv (Iso.refl M) h σ)
  let ψ' : (SmoothRep.pullbackFunctor eD).obj σ ≅ σ := ψ
  have hnat : ∀ a : σ ⟶ σ, D.pieceFunctor.map a ≫ iD.hom =
      iD.hom ≫ SmoothRep.toRep.map ((SmoothRep.pullbackFunctor eD).map a) := by
    intro a
    ext y
    exact D.fullPieceEquiv_naturality a y
  refine ⟨iD.hom ≫ SmoothRep.toRep.map ψ'.hom, ?_⟩
  have hfun : (fun a : σ ⟶ σ => D.pieceFunctor.map a ≫ iD.hom ≫ SmoothRep.toRep.map ψ'.hom) =
      (fun c => iD.hom ≫ c) ∘ (fun b => SmoothRep.toRep.map b) ∘ (fun b => b ≫ ψ'.hom) ∘
        (fun a => (SmoothRep.pullbackFunctor eD).map a) := by
    funext a
    simp only [Function.comp_apply]
    rw [← Category.assoc, hnat, Category.assoc, ← CategoryTheory.Functor.map_comp]
  rw [hfun]
  refine Function.Bijective.comp ?_ (Function.Bijective.comp ?_ (Function.Bijective.comp ?_ ?_))
  · refine Function.bijective_iff_has_inverse.mpr ⟨fun c => iD.inv ≫ c, fun c => ?_, fun c => ?_⟩
    · exact iD.inv_hom_id_assoc c
    · exact iD.hom_inv_id_assoc c
  · exact (Functor.FullyFaithful.ofFullyFaithful SmoothRep.toRep).map_bijective _ _
  · refine Function.bijective_iff_has_inverse.mpr ⟨fun c => c ≫ ψ'.inv, fun c => ?_, fun c => ?_⟩
    · simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]
    · simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  · exact (SmoothRep.pullbackEquivalence eD).fullyFaithfulFunctor.map_bijective _ _

omit [ValuativeRel k] [IsNonarchimedeanLocalField k] in
/-- For a supercuspidal `σ`, every map from a piece of `σ` to `σ` vanishes as soon as, at a full
datum, every map from the pullback of `σ` along the recovered automorphism of `M(F)` to `σ`
vanishes: a proper source intersection gives the zero piece by supercuspidality, and a full one
gives a piece isomorphic to that pullback. -/
theorem eq_zero_of_pullback_hom_eq_zero
    (σ : letI := leviPointTopology l hl; SmoothRep.{0, u, max u v} ℂ (rationalPoints M))
    (hsc : haveI := hl.isConnectedReductive.isAffineHom
      letI := leviPointTopology l hl
      haveI := leviPoints_locallyCompactSpace p l hp hl
      haveI := leviPoints_nonarchimedeanGroup p l hp hl
      IsSupercuspidal σ)
    (hfull : letI := leviPointTopology l hl
      ∀ (h : IsIso D.p') (f : SmoothRep.pullback (D.fullTargetPointsEquiv (Iso.refl M) h) σ ⟶ σ),
        f = 0)
    (g : letI := leviPointTopology l hl; D.pieceFunctor.obj σ ⟶ SmoothRep.toRep.obj σ) :
    g = 0 := by
  have := hl.isConnectedReductive.isAffineHom
  let := leviPointTopology l hl
  have := leviPoints_locallyCompactSpace p l hp hl
  have := leviPoints_nonarchimedeanGroup p l hp hl
  by_cases h : IsIso D.p'
  · let eD := D.fullTargetPointsEquiv (Iso.refl M) h
    let iD : D.pieceFunctor.obj σ ≅ SmoothRep.toRep.obj (SmoothRep.pullback eD σ) :=
      Rep.mkIso (D.fullTargetPieceEquiv (Iso.refl M) h σ)
    have hmap : SmoothRep.toRep.map (SmoothRep.toRep.preimage (iD.inv ≫ g)) = iD.inv ≫ g :=
      SmoothRep.toRep.map_preimage _
    rw [hfull h (SmoothRep.toRep.preimage (iD.inv ≫ g)), Functor.map_zero] at hmap
    calc g = iD.hom ≫ iD.inv ≫ g := (iD.hom_inv_id_assoc g).symm
      _ = 0 := by rw [← hmap, Limits.comp_zero]
  · have : Subsingleton (D.pieceFunctor.obj σ) := D.subsingleton_pieceFunctor_obj σ
      (hsc _ _ _ D.p' D.l' D.r' D.hp' D.hl' D.hr' D.hmul' h)
    ext y
    rw [Subsingleton.elim y 0, map_zero, map_zero]

/-- At a self-intersection datum whose point `z` lies in `W(D)`, that is `z` normalizes `M`
through `φ` with `π ∘ φ` an unramified twist of `π`, the piece of `Π_D = ind_{⁰M}^M ρ₀` is
isomorphic to `Π_D` compatibly with the action of `End(Π_D)`: precomposition with the piece
functor's maps, followed by one fixed map `θ`, is a bijection `End(Π_D) ≃ Hom(piece, Π_D)`. -/
theorem exists_bijective_of_witness :
    haveI := hl.isConnectedReductive.isAffineHom
    haveI : IsAffine M.X.left := isAffine_of_isAffineHom M.X.hom
    haveI := hl.isConnectedReductive.smooth
    letI : TopologicalSpace (rationalPoints M) := leviPointTopology l hl
    haveI : LocallyCompactSpace (rationalPoints M) := leviPoints_locallyCompactSpace p l hp hl
    haveI : NonarchimedeanGroup (rationalPoints M) := leviPoints_nonarchimedeanGroup p l hp hl
    ∀ π : SmoothRep.{0, u, v} ℂ (rationalPoints M), π.IsIrreducible →
    ∀ ρ₀ : SmoothRep.{0, u, v} ℂ (Plancherel.rationalCommonNormKernel M), ρ₀.IsIrreducible →
    ∀ j : ρ₀ ⟶ SmoothRep.restrictSubgroup (Plancherel.rationalCommonNormKernel M) π,
      Function.Injective (SmoothRep.hom j) →
    ∀ (φ : M ≅ M) (e : rationalPoints M ≃ₜ* rationalPoints M)
      (χ : Plancherel.unramifiedCharacters
        (fun χ : rationalCharacters M => (Plancherel.rationalNormCharacters M χ).toMul)),
      φ.hom ≫ l ≫ p = l ≫ p ≫ (G.innerIso z).hom →
      (∀ m, e m = rationalPoints.map φ.hom m) →
      Nonempty (SmoothRep.pullback e π ≅
        π.twist χ.val.toMonoidHom (Plancherel.unramifiedCharacter_isOpen_ker _ χ)) →
      ∃ θ : D.pieceFunctor.obj (CuspidalSupport.rationalNormKernelSummandInduction M ρ₀) ⟶
          SmoothRep.toRep.obj (CuspidalSupport.rationalNormKernelSummandInduction M ρ₀),
        Function.Bijective (fun a : CuspidalSupport.rationalNormKernelSummandInduction M ρ₀ ⟶
            CuspidalSupport.rationalNormKernelSummandInduction M ρ₀ =>
          D.pieceFunctor.map a ≫ θ) := by
  have := hl.isConnectedReductive.isAffineHom
  have : IsAffine M.X.left := isAffine_of_isAffineHom M.X.hom
  have := hl.isConnectedReductive.smooth
  let := leviPointTopology l hl
  have := leviPoints_locallyCompactSpace p l hp hl
  have := leviPoints_nonarchimedeanGroup p l hp hl
  intro π hπ ρ₀ hρ₀ j hj φ e χ hφ he ⟨iso⟩
  have h : IsIso D.p' := D.isIso_p'_of_normalizes φ hφ
  have hconj := D.fullTargetConjugacy_hom_eq φ hφ
  have heD : D.fullTargetPointsEquiv (Iso.refl M) h = e := by
    ext m
    rw [fullTargetPointsEquiv_apply, he, hconj]
  have he' : ∀ x, e x ∈ Plancherel.rationalCommonNormKernel M ↔
      x ∈ Plancherel.rationalCommonNormKernel M := fun x => by
    rw [he x]
    exact Geometry.Building.ValuationBuildingData.mem_rationalCommonNormKernel_mapIso_iff φ x
  obtain ⟨ψ⟩ := CuspidalSupport.nonempty_pullback_rationalNormKernelSummandInduction_iso M
    hl.isConnectedReductive e he' π hπ ρ₀ hρ₀ j hj χ _ iso
  subst heD
  have key := D.exists_bijective_of_pullback_iso
    (CuspidalSupport.rationalNormKernelSummandInduction M ρ₀) h
  have key2 := key ψ
  exact key2

/-- At a self-intersection datum whose point `z` does not lie in `W(D)`, every map from the
piece of `Π_D` to `Π_D` vanishes: if the source intersection is proper the piece is zero by
supercuspidality, and otherwise the piece is a pullback of `Π_D` and a nonzero map would put
`z` in `W(D)` (`exists_pullback_iso_twist_of_hom_ne_zero`). -/
theorem eq_zero_of_not_witness :
    haveI := hl.isConnectedReductive.isAffineHom
    haveI : IsAffine M.X.left := isAffine_of_isAffineHom M.X.hom
    haveI := hl.isConnectedReductive.smooth
    letI : TopologicalSpace (rationalPoints M) := leviPointTopology l hl
    haveI : LocallyCompactSpace (rationalPoints M) := leviPoints_locallyCompactSpace p l hp hl
    haveI : NonarchimedeanGroup (rationalPoints M) := leviPoints_nonarchimedeanGroup p l hp hl
    ∀ π : SmoothRep.{0, u, v} ℂ (rationalPoints M), π.IsIrreducible →
    ∀ ρ₀ : SmoothRep.{0, u, v} ℂ (Plancherel.rationalCommonNormKernel M),
    ∀ j : ρ₀ ⟶ SmoothRep.restrictSubgroup (Plancherel.rationalCommonNormKernel M) π,
      Function.Injective (SmoothRep.hom j) →
      IsSupercuspidal (CuspidalSupport.rationalNormKernelSummandInduction M ρ₀) →
      (¬ ∃ (φ : M ≅ M) (e : rationalPoints M ≃ₜ* rationalPoints M)
          (χ : Plancherel.unramifiedCharacters
            (fun χ : rationalCharacters M => (Plancherel.rationalNormCharacters M χ).toMul)),
        φ.hom ≫ l ≫ p = l ≫ p ≫ (G.innerIso z).hom ∧
          (∀ m, e m = rationalPoints.map φ.hom m) ∧
          Nonempty (SmoothRep.pullback e π ≅
            π.twist χ.val.toMonoidHom (Plancherel.unramifiedCharacter_isOpen_ker _ χ))) →
      ∀ g : D.pieceFunctor.obj (CuspidalSupport.rationalNormKernelSummandInduction M ρ₀) ⟶
          SmoothRep.toRep.obj (CuspidalSupport.rationalNormKernelSummandInduction M ρ₀),
        g = 0 := by
  have := hl.isConnectedReductive.isAffineHom
  have : IsAffine M.X.left := isAffine_of_isAffineHom M.X.hom
  have := hl.isConnectedReductive.smooth
  let := leviPointTopology l hl
  have := leviPoints_locallyCompactSpace p l hp hl
  have := leviPoints_nonarchimedeanGroup p l hp hl
  intro π hπ ρ₀ j hj hsc hW
  have key := D.eq_zero_of_pullback_hom_eq_zero
    (CuspidalSupport.rationalNormKernelSummandInduction M ρ₀) hsc
  intro g
  refine key ?_ g
  intro h f
  by_contra hf
  have he : ∀ x, D.fullTargetPointsEquiv (Iso.refl M) h x ∈
      Plancherel.rationalCommonNormKernel M ↔ x ∈ Plancherel.rationalCommonNormKernel M :=
    fun x => by
      rw [fullTargetPointsEquiv_apply]
      exact Geometry.Building.ValuationBuildingData.mem_rationalCommonNormKernel_mapIso_iff _ x
  obtain ⟨χ, hχ⟩ := CuspidalSupport.exists_pullback_iso_twist_of_hom_ne_zero M
    hl.isConnectedReductive (D.fullTargetPointsEquiv (Iso.refl M) h) he π hπ ρ₀ j hj f hf
  exact hW ⟨(D.fullTargetConjugacy (Iso.refl M) h).val, D.fullTargetPointsEquiv (Iso.refl M) h, χ,
    (D.fullTargetConjugacy (Iso.refl M) h).property,
    fun m => D.fullTargetPointsEquiv_apply (Iso.refl M) h m, hχ _⟩

end GeometricLemmaIntersectionDatum

end Pieces

section Assembly

variable {k : Type u} [Field k] [ValuativeRel k] [TopologicalSpace k]
  [IsNonarchimedeanLocalField k] [T2Space k]
  {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]

local instance inducedProgeneratorAssemblyAmbientTopology :
    TopologicalSpace (rationalPoints G) :=
  RationalPointFamily.pointTopology

variable [LocallyCompactSpace (rationalPoints G)] [NonarchimedeanGroup (rationalPoints G)]
  {P M N : GroupScheme (Spec (CommRingCat.of k))}

/-- The actual-group form of `W(D)`: the double cosets `P(F) w P(F)` of the points `w` of
`G(F)` normalizing `M` through some `φ : M ≅ M` with `φ ∘ (l ≫ p) = (l ≫ p) ∘ inn(w)`, such
that `π ∘ φ` is an unramified twist of `π`. This is the set `W` of
`InducedProgeneratorEndFreeStatement`. -/
def twistStabilizerDoubleCosets (p : P ⟶ G) (l : M ⟶ P) (hp : IsParabolicSubgroup p)
    (hl : IsRationalLeviSubgroup l)
    (π : letI := leviPointTopology l hl; SmoothRep.{0, u, v} ℂ (rationalPoints M)) :
    Set (DoubleCoset.Quotient (pointImage p : Set (rationalPoints G))
      (pointImage p : Set (rationalPoints G))) :=
  haveI := hl.isConnectedReductive.isAffineHom
  haveI : IsAffine M.X.left := isAffine_of_isAffineHom M.X.hom
  haveI := hl.isConnectedReductive.smooth
  letI : TopologicalSpace (rationalPoints M) := leviPointTopology l hl
  haveI : LocallyCompactSpace (rationalPoints M) := leviPoints_locallyCompactSpace p l hp hl
  haveI : NonarchimedeanGroup (rationalPoints M) := leviPoints_nonarchimedeanGroup p l hp hl
  {x | ∃ (w : rationalPoints G) (φ : M ≅ M)
      (e : rationalPoints M ≃ₜ* rationalPoints M)
      (χ : Plancherel.unramifiedCharacters
        (fun χ : rationalCharacters M => (Plancherel.rationalNormCharacters M χ).toMul)),
    DoubleCoset.mk (pointImage p) (pointImage p) w = x ∧
      φ.hom ≫ l ≫ p = l ≫ p ≫ (G.innerIso w).hom ∧
      (∀ m, e m = rationalPoints.map φ.hom m) ∧
      Nonempty (SmoothRep.pullback e π ≅
        π.twist χ.val.toMonoidHom (Plancherel.unramifiedCharacter_isOpen_ker _ χ))}

set_option maxHeartbeats 800000 in
/-- **A basis of `End(i_P σ)` indexed by witnessed double cosets.** Let `σ` be a projective
supercuspidal smooth representation of `M(F)`, `W` a set of double cosets `P(F)\G(F)/P(F)` and
`Q` a property of points of `G(F)` such that every coset of `W` contains a point satisfying `Q`
that carries a self-intersection datum, and every point satisfying `Q` lies in a coset of `W`.
If at every datum whose point satisfies `Q` precomposition with the piece functor's maps
followed by one map `θ` is a bijection `End(σ) ≃ Hom(piece of σ, σ)`, and at every datum whose
point does not satisfy `Q` all maps from the piece of `σ` to `σ` vanish, then `End(i_P σ)` is
free over `End(σ)ᵐᵒᵖ`, acting by precomposition with `i_P(a)`, with a basis indexed by `W`.
The proof filters `r_P i_P` by the geometric lemma, with points satisfying `Q` as
representatives of the cosets of `W`, and applies `inducedEndBasis` to the first adjunction
`r_P ⊣ i_P`. -/
theorem nonempty_inducedEndBasis_of_witnesses (hG : IsConnectedReductive G)
    (p : P ⟶ G) (l : M ⟶ P) (r : N ⟶ P) (hp : IsParabolicSubgroup p)
    (hr : LeviSubgroup.IsGeometricUnipotentRadical r) (hl : IsRationalLeviSubgroup l)
    (hmul : IsIso (subgroupMultiplication l r)) :
    haveI := hl.isConnectedReductive.isAffineHom
    letI : TopologicalSpace (rationalPoints M) := leviPointTopology l hl
    haveI : LocallyCompactSpace (rationalPoints M) := leviPoints_locallyCompactSpace p l hp hl
    haveI : NonarchimedeanGroup (rationalPoints M) := leviPoints_nonarchimedeanGroup p l hp hl
    ∀ σ : SmoothRep.{0, u, max u v} ℂ (rationalPoints M), Projective σ → IsSupercuspidal σ →
    ∀ (W : Set (DoubleCoset.Quotient (pointImage p : Set (rationalPoints G))
        (pointImage p : Set (rationalPoints G)))) (Q : rationalPoints G → Prop),
      (∀ x ∈ W, ∃ w : rationalPoints G, DoubleCoset.mk (pointImage p) (pointImage p) w = x ∧
        Q w ∧ Nonempty (GeometricLemmaIntersectionDatum p l r hp hr hl hmul
          p l r hp hr hl hmul w)) →
      (∀ w, Q w → DoubleCoset.mk (pointImage p) (pointImage p) w ∈ W) →
      (∀ (w : rationalPoints G)
        (D : GeometricLemmaIntersectionDatum p l r hp hr hl hmul p l r hp hr hl hmul w), Q w →
        ∃ θ : D.pieceFunctor.obj σ ⟶ SmoothRep.toRep.obj σ,
          Function.Bijective (fun a : σ ⟶ σ => D.pieceFunctor.map a ≫ θ)) →
      (∀ (w : rationalPoints G)
        (D : GeometricLemmaIntersectionDatum p l r hp hr hl hmul p l r hp hr hl hmul w), ¬ Q w →
        ∀ g : D.pieceFunctor.obj σ ⟶ SmoothRep.toRep.obj σ, g = 0) →
      letI := leviInductionFunctor_additive.{u, max u v} p l r hp hr hl hmul
      letI := RepFunctorFiltration.endPrecompModule
        (leviInductionFunctor.{u, max u v} p l r hp hr hl hmul) σ
        ((leviInductionFunctor.{u, max u v} p l r hp hr hl hmul).obj σ)
      Nonempty (Module.Basis W (End σ)ᵐᵒᵖ
        ((leviInductionFunctor.{u, max u v} p l r hp hr hl hmul).obj σ ⟶
          (leviInductionFunctor.{u, max u v} p l r hp hr hl hmul).obj σ)) := by
  classical
  have := hl.isConnectedReductive.isAffineHom
  let := leviPointTopology l hl
  have := leviPoints_locallyCompactSpace p l hp hl
  have := leviPoints_nonarchimedeanGroup p l hp hl
  intro σ hproj hsc W Q hW hQW hbij hzeroQ
  -- Step 1: finitely many double cosets, ordered with open initial unions.
  obtain ⟨m₀, c₀, z₀, hz₀, ⟨D₀⟩⟩ := representedGeometricLemmaGeometry k G hG P M N P M N
    p l r hp hl hr hmul p l r hp hl hr hmul
  have : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  have : T2Space (rationalPoints G) :=
    Langlands.AlgebraicGeometry.PointTopology.rationalPoint_t2Space k G
  have : SecondCountableTopology (rationalPoints G) :=
    RationalPointFamily.reductiveRationalPoint_secondCountable k G hG
  have : SigmaCompactSpace (rationalPoints G) :=
    sigmaCompactSpace_of_locallyCompact_secondCountable
  have hfinite : Finite (DoubleCoset.Quotient
      (pointImage p : Set (rationalPoints G)) (pointImage p : Set (rationalPoints G))) :=
    Finite.of_surjective c₀ c₀.surjective
  obtain ⟨n, ⟨s⟩⟩ := Geometric.closedSubgroupOrbitOrdering (rationalPoints G) (pointImage p)
    (pointImage p) (isClosed_pointImage p hp.isClosedSubgroup)
    (isClosed_pointImage p hp.isClosedSubgroup) hfinite
  -- Step 2: representatives, points satisfying `Q` on the cosets of `W`.
  have hex : ∀ x : DoubleCoset.Quotient (pointImage p : Set (rationalPoints G))
      (pointImage p : Set (rationalPoints G)), ∃ w : rationalPoints G,
      DoubleCoset.mk (pointImage p) (pointImage p) w = x ∧ (x ∈ W → Q w) ∧
      Nonempty (GeometricLemmaIntersectionDatum p l r hp hr hl hmul
        p l r hp hr hl hmul w) := by
    intro x
    by_cases hx : x ∈ W
    · obtain ⟨w, hmk, hQ, hD⟩ := hW x hx
      exact ⟨w, hmk, fun _ => hQ, hD⟩
    · exact ⟨z₀ (c₀.symm x), by rw [hz₀, Equiv.apply_symm_apply], fun h => absurd h hx,
        ⟨D₀ _⟩⟩
  choose rep hrepmk hrepQ hrepD using hex
  have hbij' : Function.Bijective (fun x => DoubleCoset.mk (pointImage p) (pointImage p)
      ((rep x)⁻¹)⁻¹) := by
    simp only [inv_inv, hrepmk]
    exact Function.bijective_id
  obtain ⟨ε, t, ht⟩ := s.classifiedRepresentatives (fun x => (rep x)⁻¹) hbij'
  have hpt : ∀ i, (t.representative i)⁻¹ = rep (ε i) := fun i => by rw [ht i, inv_inv]
  let E : ∀ i : Fin n, GeometricLemmaIntersectionDatum p l r hp hr hl hmul
      p l r hp hr hl hmul (t.representative i)⁻¹ := fun i => by
    rw [hpt i]
    exact Classical.choice (hrepD (ε i))
  -- Step 3: the geometric-lemma filtration of `r_P i_P` and its graded pieces.
  let F := leviJacquetSupportFiltration.{u, max u v} p l r hp hr hl hmul
    p l r hp hr hl hmul t
  have hF : F.HasGradedPieces (fun i => (E i).pieceFunctor.{u, max u v}) :=
    representedGeometricLemmaSupportGraded_of_orbitComparison.{u, max u v}
      arbitraryParabolicQuotientCompact parabolicRootPresentationExistence
      representedGeometricLemmaOrbitComparison.{u, max u v}
      k G hG P M N P M N p l r hp hl hr hmul p l r hp hl hr hmul n t E
  clear_value E F
  -- Step 4: the pieces on the cosets of `W` and the other pieces.
  have hwit : ∀ i, ε i ∈ W → Q (t.representative i)⁻¹ := by
    intro i hi
    rw [hpt i]
    exact hrepQ (ε i) hi
  have hnwit : ∀ i, ε i ∉ W → ¬ Q (t.representative i)⁻¹ := by
    intro i hi hQ
    apply hi
    have h := hQW _ hQ
    rwa [hpt i, hrepmk] at h
  let S : Finset (Fin n) := Finset.univ.filter (fun i => ε i ∈ W)
  have hθex : ∀ i : Fin n, ∃ θ : (F.graded i).obj σ ⟶ SmoothRep.toRep.obj σ,
      i ∈ S → Function.Bijective (fun a : σ ⟶ σ => (F.graded i).map a ≫ θ) := by
    intro i
    by_cases hi : i ∈ S
    · obtain ⟨θ', hθ'⟩ := hbij _ (E i) (hwit i (Finset.mem_filter.mp hi).2)
      obtain ⟨gr⟩ := hF i
      refine ⟨gr.hom.app σ ≫ θ', fun _ => ?_⟩
      have hfun : (fun a : σ ⟶ σ => (F.graded i).map a ≫ gr.hom.app σ ≫ θ') =
          (fun c => gr.hom.app σ ≫ c) ∘ (fun a : σ ⟶ σ => (E i).pieceFunctor.map a ≫ θ') := by
        funext a
        simp only [Function.comp_apply]
        rw [← Category.assoc, gr.hom.naturality, Category.assoc]
      rw [hfun]
      refine Function.Bijective.comp ?_ hθ'
      refine Function.bijective_iff_has_inverse.mpr
        ⟨fun c => gr.inv.app σ ≫ c, fun c => ?_, fun c => ?_⟩
      · exact Iso.inv_hom_id_app_assoc gr _ c
      · exact Iso.hom_inv_id_app_assoc gr _ c
    · exact ⟨0, fun h => absurd h hi⟩
  choose θ hθ using hθex
  have hzero : ∀ i ∉ S, ∀ g : (F.graded i).obj σ ⟶ SmoothRep.toRep.obj σ, g = 0 := by
    intro i hi g
    have hiW : ε i ∉ W := fun h => hi (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩)
    obtain ⟨gr⟩ := hF i
    have h0 := hzeroQ _ (E i) (hnwit i hiW) (gr.inv.app σ ≫ g)
    rw [← Iso.hom_inv_id_app_assoc gr _ g, h0, Limits.comp_zero]
  have hsec : ∀ i : Fin n, ∃ s' : (F.graded i).obj σ ⟶ (F.step i.succ).representation σ,
      s' ≫ F.gradedProjection σ i = 𝟙 _ := by
    intro i
    have hρF : IsSmooth ((leviJacquetFunctor.{u, max u v} p l r hp hr hl hmul).obj
        ((leviInductionFunctor.{u, max u v} p l r hp hr hl hmul).obj σ)).representation :=
      SmoothRep.isSmooth _
    have hZ : IsSmooth ((F.step i.succ).representation σ).ρ := fun x => by
      obtain ⟨K, hK⟩ := hρF x.1
      exact ⟨K, fun g => Subtype.ext (hK g)⟩
    obtain ⟨gr⟩ := hF i
    exact (E i).exists_section_of_iso_pieceFunctor_obj σ hproj hsc hZ _
      (F.gradedProjection_surjective _ i) (gr.app σ)
  -- Step 5: the basis through the first adjunction, reindexed by `W`.
  let := leviInductionFunctor_additive.{u, max u v} p l r hp hr hl hmul
  have : (leviJacquetFunctor.{u, max u v} p l r hp hr hl hmul).Additive :=
    (leviFirstAdjunction p l r hp hr hl hmul).left_adjoint_additive
  obtain ⟨B⟩ := RepFunctorFiltration.nonempty_inducedEndBasis_of_comp_eq
    (leviFirstAdjunction p l r hp hr hl hmul) SmoothRep.toRep F σ hsec θ S hθ hzero rfl
  let eS : S ≃ W :=
    { toFun := fun i => ⟨ε i, (Finset.mem_filter.mp i.2).2⟩
      invFun := fun x => ⟨ε.symm x, Finset.mem_filter.mpr ⟨Finset.mem_univ _, by
        rw [Equiv.apply_symm_apply]
        exact x.2⟩⟩
      left_inv := fun i => Subtype.ext (ε.symm_apply_apply i.1)
      right_inv := fun x => Subtype.ext (ε.apply_symm_apply x.1) }
  let _ := RepFunctorFiltration.endPrecompModule
    (leviInductionFunctor.{u, max u v} p l r hp hr hl hmul) σ
    ((leviInductionFunctor.{u, max u v} p l r hp hr hl hmul).obj σ)
  exact ⟨B.reindex eS⟩

/-- **Renard VI.10.4, the basis of `End(i_P Π_D)`, assuming `Π_D` projective and
supercuspidal.** `End(i_P Π_D)` is free over `End(Π_D)ᵐᵒᵖ`, acting by precomposition with
`i_P(a)`, with a basis indexed by `W(D)`: `nonempty_inducedEndBasis_of_witnesses` for
`σ = Π_D`, with the points of `W(D)` as witnesses. -/
theorem nonempty_inducedProgeneratorEndBasis (hG : IsConnectedReductive G)
    (p : P ⟶ G) (l : M ⟶ P) (r : N ⟶ P) (hp : IsParabolicSubgroup p)
    (hr : LeviSubgroup.IsGeometricUnipotentRadical r) (hl : IsRationalLeviSubgroup l)
    (hmul : IsIso (subgroupMultiplication l r)) :
    haveI := hl.isConnectedReductive.isAffineHom
    haveI : IsAffine M.X.left := isAffine_of_isAffineHom M.X.hom
    haveI := hl.isConnectedReductive.smooth
    letI : TopologicalSpace (rationalPoints M) := leviPointTopology l hl
    haveI : LocallyCompactSpace (rationalPoints M) := leviPoints_locallyCompactSpace p l hp hl
    haveI : NonarchimedeanGroup (rationalPoints M) := leviPoints_nonarchimedeanGroup p l hp hl
    ∀ π : SmoothRep.{0, u, v} ℂ (rationalPoints M), π.IsIrreducible →
    ∀ ρ₀ : SmoothRep.{0, u, v} ℂ (Plancherel.rationalCommonNormKernel M), ρ₀.IsIrreducible →
    ∀ j : ρ₀ ⟶ SmoothRep.restrictSubgroup (Plancherel.rationalCommonNormKernel M) π,
      Function.Injective (SmoothRep.hom j) →
      Projective (CuspidalSupport.rationalNormKernelSummandInduction M ρ₀) →
      IsSupercuspidal (CuspidalSupport.rationalNormKernelSummandInduction M ρ₀) →
      letI := leviInductionFunctor_additive.{u, max u v} p l r hp hr hl hmul
      letI := RepFunctorFiltration.endPrecompModule
        (leviInductionFunctor.{u, max u v} p l r hp hr hl hmul)
        (CuspidalSupport.rationalNormKernelSummandInduction M ρ₀)
        ((leviInductionFunctor.{u, max u v} p l r hp hr hl hmul).obj
          (CuspidalSupport.rationalNormKernelSummandInduction M ρ₀))
      Nonempty (Module.Basis (twistStabilizerDoubleCosets p l hp hl π)
        (End (CuspidalSupport.rationalNormKernelSummandInduction M ρ₀))ᵐᵒᵖ
        ((leviInductionFunctor.{u, max u v} p l r hp hr hl hmul).obj
            (CuspidalSupport.rationalNormKernelSummandInduction M ρ₀) ⟶
          (leviInductionFunctor.{u, max u v} p l r hp hr hl hmul).obj
            (CuspidalSupport.rationalNormKernelSummandInduction M ρ₀))) := by
  have := hl.isConnectedReductive.isAffineHom
  have : IsAffine M.X.left := isAffine_of_isAffineHom M.X.hom
  have := hl.isConnectedReductive.smooth
  let := leviPointTopology l hl
  have := leviPoints_locallyCompactSpace p l hp hl
  have := leviPoints_nonarchimedeanGroup p l hp hl
  intro π hπ ρ₀ hρ₀ jρ hjρ hproj hsc
  have hW : ∀ x ∈ twistStabilizerDoubleCosets p l hp hl π, ∃ w : rationalPoints G,
      DoubleCoset.mk (pointImage p) (pointImage p) w = x ∧
      (∃ (φ : M ≅ M) (e : rationalPoints M ≃ₜ* rationalPoints M)
        (χ : Plancherel.unramifiedCharacters
          (fun χ : rationalCharacters M => (Plancherel.rationalNormCharacters M χ).toMul)),
        φ.hom ≫ l ≫ p = l ≫ p ≫ (G.innerIso w).hom ∧
          (∀ m, e m = rationalPoints.map φ.hom m) ∧
          Nonempty (SmoothRep.pullback e π ≅
            π.twist χ.val.toMonoidHom (Plancherel.unramifiedCharacter_isOpen_ker _ χ))) ∧
      Nonempty (GeometricLemmaIntersectionDatum p l r hp hr hl hmul
        p l r hp hr hl hmul w) := by
    rintro x ⟨w, φ, e, χ, hmk, hφ, he, hiso⟩
    obtain ⟨T, i, hi, t, ht⟩ :=
      ParabolicLeviTorus.exists_maximalSplitTorus_factor parabolicDynamic hG hp hl
    have hφ' : φ.inv ≫ l ≫ p ≫ (G.innerIso w).hom = l ≫ p := by
      rw [← hφ, Iso.inv_hom_id_assoc]
    refine ⟨w, hmk, ⟨φ, e, χ, hφ, he, hiso⟩,
      ⟨geometricLemmaIntersectionDatumOfTorusFactors parabolicDynamic hG
        p l r hp hr hl hmul p l r hp hr hl hmul w i hi t ht (t ≫ φ.inv) ?_⟩⟩
    rw [Category.assoc, hφ', ht]
  have key := nonempty_inducedEndBasis_of_witnesses hG p l r hp hr hl hmul
    (CuspidalSupport.rationalNormKernelSummandInduction M ρ₀) hproj hsc
    (twistStabilizerDoubleCosets p l hp hl π)
    (fun w => ∃ (φ : M ≅ M) (e : rationalPoints M ≃ₜ* rationalPoints M)
        (χ : Plancherel.unramifiedCharacters
          (fun χ : rationalCharacters M => (Plancherel.rationalNormCharacters M χ).toMul)),
        φ.hom ≫ l ≫ p = l ≫ p ≫ (G.innerIso w).hom ∧
          (∀ m, e m = rationalPoints.map φ.hom m) ∧
          Nonempty (SmoothRep.pullback e π ≅
            π.twist χ.val.toMonoidHom (Plancherel.unramifiedCharacter_isOpen_ker _ χ)))
    hW (fun w ⟨φ, e, χ, hφ, he, hiso⟩ => ⟨w, φ, e, χ, rfl, hφ, he, hiso⟩)
  have key2 := key (fun w D ⟨φ, e, χ, hφ, he, hiso⟩ =>
    D.exists_bijective_of_witness π hπ ρ₀ hρ₀ jρ hjρ φ e χ hφ he hiso)
  have key3 := key2 (fun w D hnQ => D.eq_zero_of_not_witness π hπ ρ₀ jρ hjρ hsc hnQ)
  exact key3

/-- **The basis of `End(i_P Π_D)` indexed by `W(D)`** (Renard VI.10.4), for `Π_D` projective
and supercuspidal: `End(i_P Π_D)` is free over `End(Π_D)ᵐᵒᵖ`, acting by precomposition with
`i_P(a)`, with this basis indexed by the set `twistStabilizerDoubleCosets p l hp hl π`. The basis
is a choice from `nonempty_inducedProgeneratorEndBasis`. -/
def inducedProgeneratorEndBasis (hG : IsConnectedReductive G)
    (p : P ⟶ G) (l : M ⟶ P) (r : N ⟶ P) (hp : IsParabolicSubgroup p)
    (hr : LeviSubgroup.IsGeometricUnipotentRadical r) (hl : IsRationalLeviSubgroup l)
    (hmul : IsIso (subgroupMultiplication l r)) :
    haveI := hl.isConnectedReductive.isAffineHom
    haveI : IsAffine M.X.left := isAffine_of_isAffineHom M.X.hom
    haveI := hl.isConnectedReductive.smooth
    letI : TopologicalSpace (rationalPoints M) := leviPointTopology l hl
    haveI : LocallyCompactSpace (rationalPoints M) := leviPoints_locallyCompactSpace p l hp hl
    haveI : NonarchimedeanGroup (rationalPoints M) := leviPoints_nonarchimedeanGroup p l hp hl
    ∀ π : SmoothRep.{0, u, v} ℂ (rationalPoints M), π.IsIrreducible →
    ∀ ρ₀ : SmoothRep.{0, u, v} ℂ (Plancherel.rationalCommonNormKernel M), ρ₀.IsIrreducible →
    ∀ j : ρ₀ ⟶ SmoothRep.restrictSubgroup (Plancherel.rationalCommonNormKernel M) π,
      Function.Injective (SmoothRep.hom j) →
      Projective (CuspidalSupport.rationalNormKernelSummandInduction M ρ₀) →
      IsSupercuspidal (CuspidalSupport.rationalNormKernelSummandInduction M ρ₀) →
      letI := leviInductionFunctor_additive.{u, max u v} p l r hp hr hl hmul
      letI := RepFunctorFiltration.endPrecompModule
        (leviInductionFunctor.{u, max u v} p l r hp hr hl hmul)
        (CuspidalSupport.rationalNormKernelSummandInduction M ρ₀)
        ((leviInductionFunctor.{u, max u v} p l r hp hr hl hmul).obj
          (CuspidalSupport.rationalNormKernelSummandInduction M ρ₀))
      Module.Basis (twistStabilizerDoubleCosets p l hp hl π)
        (End (CuspidalSupport.rationalNormKernelSummandInduction M ρ₀))ᵐᵒᵖ
        ((leviInductionFunctor.{u, max u v} p l r hp hr hl hmul).obj
            (CuspidalSupport.rationalNormKernelSummandInduction M ρ₀) ⟶
          (leviInductionFunctor.{u, max u v} p l r hp hr hl hmul).obj
            (CuspidalSupport.rationalNormKernelSummandInduction M ρ₀)) :=
  fun π hπ ρ₀ hρ₀ j hj hproj hsc => Classical.choice
    (nonempty_inducedProgeneratorEndBasis hG p l r hp hr hl hmul π hπ ρ₀ hρ₀ j hj hproj hsc)

/-- **Renard VI.10.4, the third conjunct of `InducedProgeneratorEndFreeStatement`, assuming
`Π_D` projective and supercuspidal.** `W(D)` is finite and there are `b₁, …, b_n` in
`End(i_P Π_D)`, `n = |W(D)|`, such that every `x` is uniquely `∑ i_P(aᵢ) ≫ bᵢ` with
`aᵢ ∈ End(Π_D)`. -/
theorem inducedProgeneratorEnd_expansion (hG : IsConnectedReductive G)
    (p : P ⟶ G) (l : M ⟶ P) (r : N ⟶ P) (hp : IsParabolicSubgroup p)
    (hr : LeviSubgroup.IsGeometricUnipotentRadical r) (hl : IsRationalLeviSubgroup l)
    (hmul : IsIso (subgroupMultiplication l r)) :
    haveI := hl.isConnectedReductive.isAffineHom
    haveI : IsAffine M.X.left := isAffine_of_isAffineHom M.X.hom
    haveI := hl.isConnectedReductive.smooth
    letI : TopologicalSpace (rationalPoints M) := leviPointTopology l hl
    haveI : LocallyCompactSpace (rationalPoints M) := leviPoints_locallyCompactSpace p l hp hl
    haveI : NonarchimedeanGroup (rationalPoints M) := leviPoints_nonarchimedeanGroup p l hp hl
    ∀ π : SmoothRep.{0, u, v} ℂ (rationalPoints M), π.IsIrreducible →
    ∀ ρ₀ : SmoothRep.{0, u, v} ℂ (Plancherel.rationalCommonNormKernel M), ρ₀.IsIrreducible →
    ∀ j : ρ₀ ⟶ SmoothRep.restrictSubgroup (Plancherel.rationalCommonNormKernel M) π,
      Function.Injective (SmoothRep.hom j) →
      Projective (CuspidalSupport.rationalNormKernelSummandInduction M ρ₀) →
      IsSupercuspidal (CuspidalSupport.rationalNormKernelSummandInduction M ρ₀) →
      let W := twistStabilizerDoubleCosets p l hp hl π
      let piD := CuspidalSupport.rationalNormKernelSummandInduction M ρ₀
      let I := leviInductionFunctor p l r hp hr hl hmul
      W.Finite ∧
        ∃ b : Fin W.ncard → (I.obj piD ⟶ I.obj piD),
          ∀ x : I.obj piD ⟶ I.obj piD,
            ∃! a : Fin W.ncard → (piD ⟶ piD), x = ∑ i, I.map (a i) ≫ b i := by
  have := hl.isConnectedReductive.isAffineHom
  have : IsAffine M.X.left := isAffine_of_isAffineHom M.X.hom
  have := hl.isConnectedReductive.smooth
  let := leviPointTopology l hl
  have := leviPoints_locallyCompactSpace p l hp hl
  have := leviPoints_nonarchimedeanGroup p l hp hl
  intro π hπ ρ₀ hρ₀ jρ hjρ hproj hsc W piD I
  have hfin : W.Finite := normalizerDoubleCosets_subset_finite hG p l hp hl W
    (fun _ ⟨w, φ, _, _, hmk, hφ, _, _⟩ => ⟨w, φ, hmk, hφ⟩)
  refine ⟨hfin, ?_⟩
  have := hfin.to_subtype
  let := leviInductionFunctor_additive.{u, max u v} p l r hp hr hl hmul
  exact RepFunctorFiltration.existsUnique_precomp_expansion_of_basis
    (leviInductionFunctor.{u, max u v} p l r hp hr hl hmul)
    (CuspidalSupport.rationalNormKernelSummandInduction M ρ₀)
    ((leviInductionFunctor.{u, max u v} p l r hp hr hl hmul).obj
      (CuspidalSupport.rationalNormKernelSummandInduction M ρ₀))
    ((Finite.equivFin (twistStabilizerDoubleCosets p l hp hl π)).trans
      (finCongr (Nat.card_coe_set_eq _)))
    (inducedProgeneratorEndBasis hG p l r hp hr hl hmul π hπ ρ₀ hρ₀ jρ hjρ hproj hsc)

end Assembly

end Langlands.Aubert.General.RepresentedParabolic
