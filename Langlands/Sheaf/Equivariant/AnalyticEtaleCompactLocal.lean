import Langlands.Sheaf.Equivariant.AnalyticEtaleSupportAction
import Langlands.Sheaf.Equivariant.TwistedFiniteGlobalSections

/-! # Compact supports and local lifted actions -/

noncomputable section

namespace Langlands.Sheaf.Equivariant.Analytic

open CategoryTheory CategoryTheory.Limits Opposite
open Langlands.Analytic Langlands.Analytic.SaturatedAtlasPresentation
open Langlands.Sheaf.Equivariant.TwistedOver Langlands.Sheaf.PointSupport

universe u v uL z

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
variable (L : Type uL) [NormedField L] [NormedAlgebra K L]
variable {X : LocalizedCategory.{u, v, v} (K := K)}
variable (h : ∀ x : (localizedFieldPointFunctor L).obj X, EtaleSite.PointAxioms L x)
variable {R : Type (max u (v + 1) uL)} [CommRing R]
variable {G : Type z} [Group G] (ρ : G →* Aut X)

/-- Equality after restriction along a twisted arrow implies equality of
global germs over its underlying image, assuming point lifting. -/
theorem etaleGlobalGermMap_eq_of_twisted_restriction_eq
    (hlift : EtalePointLifting L (X := X))
    (F : Sheaf (twistedEtaleTopology ρ) (ModuleCat.{max u (v + 1) uL} R))
    {U : TwistedOver etale ρ} (f : U ⟶ base etale ρ)
    (s t : F.obj.obj (op (base etale ρ)))
    (hst : F.obj.map f.op s = F.obj.map f.op t)
    (x : (localizedFieldPointFunctor L).obj X)
    (hx : pointProjection L X x ∈ Set.range (localizedSpaceFunctor.map (Hom.left f))) :
    etaleGlobalGermMap L h
        ((TwistedOver.restriction ρ (etaleTopology X)
          (ModuleCat.{max u (v + 1) uL} R)).obj F) s x =
      etaleGlobalGermMap L h
        ((TwistedOver.restriction ρ (etaleTopology X)
          (ModuleCat.{max u (v + 1) uL} R)).obj F) t x := by
  let V := (translate etale ρ (Hom.twist f)).obj U.obj
  let m : V ⟶ etaleSelf X := untwist (Hom.twist f) f rfl
  have hfac := relabel_comp_ι_map_untwist (Hom.twist f) f rfl
  have hres : ((ι etale ρ).op ⋙ F.obj).map m.op s =
      ((ι etale ρ).op ⋙ F.obj).map m.op t := by
    change F.obj.map ((ι etale ρ).map m).op s =
      F.obj.map ((ι etale ρ).map m).op t
    apply (ConcreteCategory.bijective_of_isIso
      (F.obj.map (relabel ρ (Hom.twist f) U.obj).op)).1
    have hmap : F.obj.map ((ι etale ρ).map m).op ≫
        F.obj.map (relabel ρ (Hom.twist f) U.obj).op = F.obj.map f.op := by
      rw [← F.obj.map_comp, ← op_comp]
      exact congrArg (fun k : U ⟶ base etale ρ => F.obj.map k.op) hfac
    change (F.obj.map ((ι etale ρ).map m).op ≫
        F.obj.map (relabel ρ (Hom.twist f) U.obj).op) s =
      (F.obj.map ((ι etale ρ).map m).op ≫
        F.obj.map (relabel ρ (Hom.twist f) U.obj).op) t
    rw [hmap]
    exact hst
  have hm : Hom.left f = (show U.obj.left ⟶ X from V.hom) := by
    have hw := Hom.w f
    change Hom.left f ≫ 𝟙 X = V.hom at hw
    exact (Category.comp_id _).symm.trans hw
  have hx' : pointProjection L X x ∈ Set.range (localizedSpaceFunctor.map V.hom) := by
    change pointProjection L X x ∈
      Set.range (localizedSpaceFunctor.map (show U.obj.left ⟶ X from V.hom))
    rw [← hm]
    exact hx
  have hzero : x ∉ support (etalePoints L h) ((ι etale ρ).op ⋙ F.obj) (s - t) :=
    (not_mem_support_etaleSelf_iff L h hlift _ _ x).2
      ⟨V, m, hx', by
        change F.obj.map ((ι etale ρ).map m).op (s - t) = 0
        exact (map_sub _ s t).trans (sub_eq_zero.mpr hres)⟩
  have hgerm :
      etaleGlobalGermMap L h
        ((TwistedOver.restriction ρ (etaleTopology X)
          (ModuleCat.{max u (v + 1) uL} R)).obj F) (s - t) x = 0 := by
    by_contra hn
    exact hzero ⟨etaleSelfPoint L h x, hn⟩
  apply sub_eq_zero.mp
  exact (congrFun (map_sub
    (etaleGlobalGermMap L h
      ((TwistedOver.restriction ρ (etaleTopology X)
        (ModuleCat.{max u (v + 1) uL} R)).obj F)) s t) x).symm.trans hgerm

variable [TopologicalSpace G] [IsTopologicalGroup G]

/-- A discrete restriction along a lifted local action agrees with its
translates over an invariant image for a sufficiently small open subgroup. -/
theorem exists_openSubgroup_twisted_restriction_eq
    (F : (TwistedOver etale ρ)ᵒᵖ ⥤ ModuleCat.{max u (v + 1) uL} R)
    {U : TwistedOver etale ρ} {H : OpenSubgroup G}
    {b : (H : Subgroup G) →* (End U)ᵐᵒᵖ} (hb : IsLift b)
    (f : U ⟶ base etale ρ) (s : F.obj (op (base etale ρ)))
    (hs : IsDiscreteSection F b (F.map f.op s)) :
    ∃ M : OpenSubgroup G,
      (∀ g ∈ M, ∀ y ∈ Set.range (localizedSpaceFunctor.map (Hom.left f)),
        localizedSpaceFunctor.map (ρ g).asIso.hom y ∈
          Set.range (localizedSpaceFunctor.map (Hom.left f))) ∧
      ∀ g ∈ M, F.map f.op (actionRepresentation F (baseAction etale ρ) g s) =
        F.map f.op s := by
  obtain ⟨N, hNH, hN⟩ := hs
  obtain ⟨M, -, hM⟩ := isLocallyEquivariant_to_base hb f N hNH
  refine ⟨M, ?_, ?_⟩
  · intro g hg y hy
    obtain ⟨z, rfl⟩ := hy
    obtain ⟨k, -, hk⟩ := hM ⟨g⁻¹, trivial⟩ (M.inv_mem hg)
    have he : Hom.left (b k).unop.asHom ≫ Hom.left f =
        Hom.left f ≫ (ρ g).asIso.hom := by
      have he' := congrArg Hom.left hk
      change Hom.left (b k).unop.asHom ≫ Hom.left f =
        Hom.left f ≫ (ρ (g⁻¹)⁻¹).asIso.hom at he'
      simpa only [inv_inv] using he'
    refine ⟨localizedSpaceFunctor.map (Hom.left (b k).unop.asHom) z, ?_⟩
    have hcomp := congrArg (fun m : U.obj.left ⟶ X => localizedSpaceFunctor.map m z) he
    exact (localizedSpaceFunctor.map_comp_apply (Hom.left (b k).unop.asHom)
      (show U.obj.left ⟶ X from Hom.left f) z).symm.trans
        (hcomp.trans (localizedSpaceFunctor.map_comp_apply
          (show U.obj.left ⟶ X from Hom.left f) (ρ g).asIso.hom z))
  · intro g hg
    obtain ⟨k, hkN, hk⟩ := hM ⟨g, trivial⟩ hg
    change F.map f.op (F.map (baseAction etale ρ g).unop.asHom.op s) = F.map f.op s
    calc
      F.map f.op (F.map (baseAction etale ρ g).unop.asHom.op s) =
          F.map (f ≫ (baseAction etale ρ g).unop.asHom).op s := by
        rw [op_comp, F.map_comp, CategoryTheory.comp_apply]
      _ = F.map ((b k).unop.asHom ≫ f).op s :=
        congrArg (fun m : U ⟶ base etale ρ => F.map m.op s) hk.symm
      _ = F.map (b k).unop.asHom.op (F.map f.op s) := by
        rw [op_comp, F.map_comp, CategoryTheory.comp_apply]
      _ = F.map f.op s := hN k hkN

/-- Local discreteness gives an open invariant neighborhood on which the
global section and its small translates have the same global germs. -/
theorem exists_open_invariant_etaleGlobalGermMap_eq
    (hlift : EtalePointLifting L (X := X))
    (hX : Function.Surjective (pointProjection L X))
    (hopen : ∀ U : EtaleSite X, IsOpenMap (localizedSpaceFunctor.map U.hom))
    (F : Sheaf (twistedEtaleTopology ρ) (ModuleCat.{max u (v + 1) uL} R))
    (hloc : (distinguishedLiftSystem ρ).IsLocallyDiscrete (twistedEtaleTopology ρ) F.obj)
    (s : F.obj.obj (op (base etale ρ))) (y : localizedSpaceFunctor.obj X) :
    ∃ (W : Set (localizedSpaceFunctor.obj X)) (M : OpenSubgroup G),
      IsOpen W ∧ y ∈ W ∧
      (∀ g ∈ M, ∀ z ∈ W, localizedSpaceFunctor.map (ρ g).asIso.hom z ∈ W) ∧
      ∀ g ∈ M, ∀ x, pointProjection L X x ∈ W →
        etaleGlobalGermMap L h
            ((TwistedOver.restriction ρ (etaleTopology X)
              (ModuleCat.{max u (v + 1) uL} R)).obj F)
            (actionRepresentation F.obj (baseAction etale ρ) g s) x =
          etaleGlobalGermMap L h
            ((TwistedOver.restriction ρ (etaleTopology X)
              (ModuleCat.{max u (v + 1) uL} R)).obj F) s x := by
  obtain ⟨x, rfl⟩ := hX y
  let S := (distinguishedLiftSystem ρ).discreteSieve F.obj s
  have hS : Sieve.functorPullback (ι etale ρ) S ∈
      etaleTopology X (etaleSelf X) := hloc _ s
  obtain ⟨V, f, hf, q, -⟩ := (h x).2 _ hS
    ⟨x, (localizedFieldPointFunctor L).map_id_apply X x⟩
  change S ((ι etale ρ).map f) at hf
  obtain ⟨U, k, p, H, b, hb, hdisc, hfac⟩ := hf
  have hx : pointProjection L X x ∈
      Set.range (localizedSpaceFunctor.map (Hom.left ((ι etale ρ).map f))) := by
    have hleft : f.left = (show V.left ⟶ X from V.hom) := by
      have hw := MorphismProperty.Over.w f
      change f.left ≫ 𝟙 X = V.hom at hw
      exact (Category.comp_id _).symm.trans hw
    refine ⟨pointProjection L V.left q.val, ?_⟩
    change localizedSpaceFunctor.map (show V.left ⟶ X from f.left)
      (pointProjection L V.left q.val) = pointProjection L X x
    exact (congrArg (fun m : V.left ⟶ X =>
      localizedSpaceFunctor.map m (pointProjection L V.left q.val)) hleft).trans
        ((pointProjection_map L V.hom q.val).symm.trans
          (congrArg (pointProjection L X) q.property))
  have hxp : pointProjection L X x ∈
      Set.range (localizedSpaceFunctor.map (Hom.left p)) := by
    obtain ⟨z, hz⟩ := hx
    refine ⟨localizedSpaceFunctor.map (Hom.left k) z, ?_⟩
    have he : Hom.left k ≫ Hom.left p =
        Hom.left ((ι etale ρ).map f) := congrArg Hom.left hfac
    exact (localizedSpaceFunctor.map_comp_apply (Hom.left k)
      (show U.obj.left ⟶ X from Hom.left p) z).symm.trans
        ((congrArg (fun m : V.left ⟶ X => localizedSpaceFunctor.map m z) he).trans hz)
  have hOp : IsOpen (Set.range (localizedSpaceFunctor.map (Hom.left p))) := by
    let U' := (translate etale ρ (Hom.twist p)).obj U.obj
    have he : Hom.left p = (show U.obj.left ⟶ X from U'.hom) := by
      have hw := Hom.w p
      change Hom.left p ≫ 𝟙 X = U'.hom at hw
      exact (Category.comp_id _).symm.trans hw
    have hrange : Set.range (localizedSpaceFunctor.map (Hom.left p)) =
        Set.range (localizedSpaceFunctor.map U'.hom) :=
      congrArg (fun m : U.obj.left ⟶ X => Set.range (localizedSpaceFunctor.map m)) he
    exact hrange.symm ▸ (hopen U').isOpen_range
  have hb' : IsLift b := isLiftSystem_liftSystem
    (ρ := ρ) (fun U => IsDistinguishedEtale U.hom) U H b hb
  obtain ⟨M, hstab, hres⟩ :=
    exists_openSubgroup_twisted_restriction_eq.{u, v, uL, z} ρ F.obj hb' p s hdisc
  refine ⟨Set.range (localizedSpaceFunctor.map (Hom.left p)), M,
    hOp, hxp, hstab, fun g hg x hx => ?_⟩
  exact etaleGlobalGermMap_eq_of_twisted_restriction_eq L h ρ hlift F p
    _ _ (hres g hg) x hx

/-- A global section with compact underlying support in a locally discrete
étale sheaf is a smooth vector, under explicit geometric support hypotheses. -/
theorem isSmoothVector_of_isCompact_etaleUnderlyingSupport
    (hlift : EtalePointLifting L (X := X))
    (hX : Function.Surjective (pointProjection L X))
    (hopen : ∀ U : EtaleSite X, IsOpenMap (localizedSpaceFunctor.map U.hom))
    (F : Sheaf (twistedEtaleTopology ρ) (ModuleCat.{max u (v + 1) uL} R))
    (hloc : (distinguishedLiftSystem ρ).IsLocallyDiscrete (twistedEtaleTopology ρ) F.obj)
    (s : F.obj.obj (op (base etale ρ)))
    (hs : IsCompact (etaleUnderlyingSupport L h ((ι etale ρ).op ⋙ F.obj) s)) :
    Langlands.IsSmoothVector (actionRepresentation F.obj (baseAction etale ρ)) s := by
  let germEq : G → (localizedFieldPointFunctor L).obj X → Prop := fun g x =>
    etaleGlobalGermMap L h
        ((TwistedOver.restriction ρ (etaleTopology X)
          (ModuleCat.{max u (v + 1) uL} R)).obj F)
        (actionRepresentation F.obj (baseAction etale ρ) g s) x =
      etaleGlobalGermMap L h
        ((TwistedOver.restriction ρ (etaleTopology X)
          (ModuleCat.{max u (v + 1) uL} R)).obj F) s x
  let p : Set (localizedSpaceFunctor.obj X) → Prop := fun S =>
    ∃ (M : OpenSubgroup G) (W : Set (localizedSpaceFunctor.obj X)), S ⊆ W ∧
      (∀ g ∈ M, ∀ y ∈ W, localizedSpaceFunctor.map (ρ g).asIso.hom y ∈ W) ∧
      ∀ g ∈ M, ∀ x, pointProjection L X x ∈ W → germEq g x
  have hp : p (etaleUnderlyingSupport L h ((ι etale ρ).op ⋙ F.obj) s) := by
    refine hs.induction_on ?_ ?_ ?_ ?_
    · exact ⟨⊤, ∅, subset_rfl, fun _ _ _ hy => hy, fun _ _ _ hx => absurd hx id⟩
    · rintro S T hST ⟨M, W, hTW, hstab, hgerm⟩
      exact ⟨M, W, hST.trans hTW, hstab, hgerm⟩
    · rintro S T ⟨M₁, W₁, hS, hstab₁, hgerm₁⟩ ⟨M₂, W₂, hT, hstab₂, hgerm₂⟩
      refine ⟨M₁ ⊓ M₂, W₁ ∪ W₂, Set.union_subset_union hS hT, ?_, ?_⟩
      · rintro g hg y (hy | hy)
        · exact Or.inl (hstab₁ g (OpenSubgroup.mem_inf.mp hg).1 y hy)
        · exact Or.inr (hstab₂ g (OpenSubgroup.mem_inf.mp hg).2 y hy)
      · rintro g hg x (hx | hx)
        · exact hgerm₁ g (OpenSubgroup.mem_inf.mp hg).1 x hx
        · exact hgerm₂ g (OpenSubgroup.mem_inf.mp hg).2 x hx
    · intro y _
      obtain ⟨W, M, hW, hyW, hstab, hgerm⟩ :=
        exists_open_invariant_etaleGlobalGermMap_eq L h ρ hlift hX hopen F hloc s y
      exact ⟨W, mem_nhdsWithin_of_mem_nhds (hW.mem_nhds hyW),
        M, W, subset_rfl, hstab, hgerm⟩
  obtain ⟨M, W, hsW, hstab, hgerm⟩ := hp
  refine ⟨M, fun g => ?_⟩
  exact actionRepresentation_eq_of_etaleGlobalGermMap_eq_on L h ρ hX F g s W hsW
    (hstab g g.property) (hgerm g g.property)

/-- Compactly supported global sections of a locally discrete étale sheaf
form a smooth representation, under point lifting, surjectivity and openness. -/
theorem isSmooth_etaleCompactRepresentation_of_locallyDiscrete
    (hlift : EtalePointLifting L (X := X))
    (hX : Function.Surjective (pointProjection L X))
    (hopen : ∀ U : EtaleSite X, IsOpenMap (localizedSpaceFunctor.map U.hom))
    (F : Sheaf (twistedEtaleTopology ρ) (ModuleCat.{max u (v + 1) uL} R))
    (hloc : (distinguishedLiftSystem ρ).IsLocallyDiscrete (twistedEtaleTopology ρ) F.obj) :
    letI := pointTopology L X
    letI := EtaleSite.pointAction L ρ
    haveI := continuousConstSMul_pointAction L ρ
    haveI := etaleSite_locallySmall_points.{u, v, uL} X
    Langlands.IsSmooth (compactRepresentation R (EtaleSite.pointEquivariance L ρ h) F.obj) := by
  let := pointTopology L X
  let := EtaleSite.pointAction L ρ
  have := continuousConstSMul_pointAction L ρ
  have := etaleSite_locallySmall_points.{u, v, uL} X
  rintro ⟨s, hs⟩
  have hcompact := (isCompactlySupported_etaleSelf_iff_isCompact_underlyingSupport
    L h hlift hX hopen ((ι etale ρ).op ⋙ F.obj) s).mp hs
  obtain ⟨M, hM⟩ :=
    isSmoothVector_of_isCompact_etaleUnderlyingSupport L h ρ hlift hX hopen F hloc s hcompact
  exact ⟨M, fun g => Subtype.ext (hM g)⟩

/-- Under the explicit support hypotheses, the canonical inclusion from smooth
compact sections of an étale `G`-sheaf is an isomorphism. -/
theorem isIso_etaleCompactInclusion
    (hlift : EtalePointLifting L (X := X))
    (hX : Function.Surjective (pointProjection L X))
    (hopen : ∀ U : EtaleSite X, IsOpenMap (localizedSpaceFunctor.map U.hom)) :
    IsIso (etaleCompactInclusion L ρ h R) := by
  let := pointTopology L X
  let := EtaleSite.pointAction L ρ
  have := continuousConstSMul_pointAction L ρ
  have := etaleSite_locallySmall_points.{u, v, uL} X
  have : ∀ F, IsIso ((etaleCompactInclusion L ρ h R).app F) := by
    intro F
    have hsm := isSmooth_etaleCompactRepresentation_of_locallyDiscrete
      L h ρ hlift hX hopen F.obj F.property
    apply (ConcreteCategory.isIso_iff_bijective _).mpr
    exact ⟨Subtype.val_injective, fun s => ⟨⟨s, hsm s⟩, rfl⟩⟩
  exact NatIso.isIso_of_isIso_app _

/-- The canonical degree-zero compact-section comparison, packaged as a
natural isomorphism under explicit geometric support hypotheses. -/
def etaleCompactSectionsIso
    (hlift : EtalePointLifting L (X := X))
    (hX : Function.Surjective (pointProjection L X))
    (hopen : ∀ U : EtaleSite X, IsOpenMap (localizedSpaceFunctor.map U.hom)) :
    etaleGSheafCompactSections L ρ h R ⋙ smoothForget R G ≅
      etaleGSheafRestriction.{u, v, uL} ρ R ⋙ etaleCompactSections L h R :=
  haveI := isIso_etaleCompactInclusion (R := R) L h ρ hlift hX hopen
  asIso (etaleCompactInclusion L ρ h R)

/-- The forward map of the comparison is the canonical compact-section inclusion. -/
theorem etaleCompactSectionsIso_hom
    (hlift : EtalePointLifting L (X := X))
    (hX : Function.Surjective (pointProjection L X))
    (hopen : ∀ U : EtaleSite X, IsOpenMap (localizedSpaceFunctor.map U.hom)) :
    (etaleCompactSectionsIso (R := R) L h ρ hlift hX hopen).hom =
      etaleCompactInclusion L ρ h R := rfl

end Langlands.Sheaf.Equivariant.Analytic
