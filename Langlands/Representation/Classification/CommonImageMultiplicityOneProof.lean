import Langlands.Representation.Classification.CommonImageMultiplicityOneStatement
import Langlands.Representation.Classification.MultiplicityOneConstituentProof
import Langlands.Representation.Filtration.MultiplicityAdditivityProof

/-!
# Strong endpoints from an actual common image

Positive detection of all nonzero quotients and subobjects makes the actual
image irreducible. The published constituent criteria then give strong
uniqueness of its quotient kernel and embedding image.
-/

noncomputable section

namespace Langlands.Classification

open CategoryTheory

universe uG uH uV uW uT

variable {G : Type uG} [Group G] [TopologicalSpace G]
  {H : Type uH} [Monoid H]

private theorem positive_zero_composite_impossible
    (F : SmoothRep.{0, uG, uV} ℂ G ⥤ Rep.{uW} ℂ H)
    [F.Additive] [F.PreservesEpimorphisms] [F.PreservesMonomorphisms]
    (I P Q : SmoothRep.{0, uG, uV} ℂ G)
    (a : P ⟶ I) (b : I ⟶ Q)
    (ha : Function.Injective (SmoothRep.hom a))
    (hb : Function.Surjective (SmoothRep.hom b))
    (hab : a ≫ b = 0)
    (τ : Rep.{uT} ℂ H) (mP mQ : ℕ)
    (hI : HasJordanHolderMultiplicity (F.obj I) τ 1)
    (hP : HasJordanHolderMultiplicity (F.obj P) τ mP)
    (hQ : HasJordanHolderMultiplicity (F.obj Q) τ mQ)
    (hmP : 0 < mP) (hmQ : 0 < mQ) : False := by
  have hFzero : F.map a ≫ F.map b = 0 := by
    rw [← F.map_comp, hab, F.map_zero]
  let : Mono a := (SmoothRep.mono_iff_injective a).mpr ha
  let : Epi b := (SmoothRep.epi_iff_surjective b).mpr hb
  let d := (F.map a).hom
  let r := (F.map b).hom
  have hd : Function.Injective d :=
    (Rep.mono_iff_injective (F.map a)).mp inferInstance
  have hr : Function.Surjective r :=
    (Rep.epi_iff_surjective (F.map b)).mp inferInstance
  have hdr (x : (F.obj P).V) : r (d x) = 0 :=
    congrArg (fun l : F.obj P ⟶ F.obj Q => l.hom x) hFzero
  let K : Rep.{uW} ℂ H := Rep.of r.ker.toRepresentation
  let i : K.ρ.IntertwiningMap (F.obj I).ρ :=
    { toLinearMap := r.ker.toSubmodule.subtype
      isIntertwining' _ := rfl }
  have hex : LinearMap.range i.toLinearMap = LinearMap.ker r.toLinearMap :=
    Submodule.range_subtype _
  obtain ⟨mK, mQ', hK, hQ', hsum⟩ :=
    jordanHolderShortExactDecomposition ℂ H K (F.obj I) (F.obj Q) τ i r
      (Submodule.injective_subtype _) hr hex 1 hI
  let k : (F.obj P).ρ.IntertwiningMap K.ρ :=
    { toLinearMap := d.toLinearMap.codRestrict r.ker.toSubmodule hdr
      isIntertwining' g := by
        ext x
        exact congrArg (fun l : (F.obj P).V →ₗ[ℂ] (F.obj I).V => l x)
          (d.isIntertwining' g) }
  have hk : Function.Injective k :=
    fun x y h => hd (congrArg Subtype.val h)
  have hle := jordanHolderInjectiveMonotonicity ℂ H (F.obj P) K τ k hk
    mP mK hP hK
  have heq := HasJordanHolderMultiplicity.unique hQ' hQ
  omega

private theorem irreducible_carrier_nontrivial
    (P : SmoothRep.{0, uG, uV} ℂ G) (hP : P.IsIrreducible) : Nontrivial P := by
  by_contra h
  have : Subsingleton P := not_nontrivial_iff_subsingleton.mp h
  let := hP
  exact (bot_ne_top : (⊥ : Subrepresentation P.representation) ≠ ⊤)
    (Subrepresentation.ext (Subsingleton.elim _ _))

/-- The exact common-image criterion, retaining a factorization of the given
nonzero map and strong uniqueness of both actual endpoints. -/
theorem commonImageMultiplicityOne :
    CommonImageMultiplicityOneStatement.{uG, uH, uV, uW, uT} := by
  intro G _ _ H _ F _ _ _ A B τ hA hB hqpos hjpos f hf
  let I := SmoothRep.image f
  let q : A ⟶ I := SmoothRep.ofHom
    { toLinearMap := (SmoothRep.hom f).toLinearMap.rangeRestrict
      isIntertwining' g := by
        ext x
        apply Subtype.ext
        exact congrArg (fun l : A →ₗ[ℂ] B => l x) ((SmoothRep.hom f).isIntertwining' g) }
  let j : I ⟶ B := SmoothRep.imageι f
  have hq : Function.Surjective (SmoothRep.hom q) := by
    rintro ⟨y, x, hx⟩
    exact ⟨x, Subtype.ext hx⟩
  have hj : Function.Injective (SmoothRep.hom j) :=
    SmoothRep.subtype_injective B (SmoothRep.hom f).range
  have hfac : f = q ≫ j := by
    have h : SmoothRep.hom f = SmoothRep.hom (q ≫ j) := by
      ext x
      rfl
    exact congrArg (fun k : A.representation.IntertwiningMap B.representation =>
      SmoothRep.ofHom k) h
  have hqne : q ≠ 0 := by
    intro h
    exact hf (by simpa [h] using hfac)
  obtain ⟨mI, hFI, hmI⟩ := hqpos I q hq hqne
  let : Epi q := (SmoothRep.epi_iff_surjective q).mpr hq
  have hFq : Function.Surjective (F.map q).hom :=
    (Rep.epi_iff_surjective (F.map q)).mp inferInstance
  have hle := jordanHolderSurjectiveMonotonicity ℂ H (F.obj A) (F.obj I) τ
    (F.map q).hom hFq 1 mI hA hFI
  have hmIone : mI = 1 := by omega
  have hFIone : HasJordanHolderMultiplicity (F.obj I) τ 1 := hmIone ▸ hFI
  have hI : I.IsIrreducible := by
    have hbot_top : (⊥ : Subrepresentation I.representation) ≠ ⊤ := by
      intro h
      apply hqne
      have hzero : SmoothRep.hom q = 0 := by
        ext x
        have hx : SmoothRep.hom q x ∈ (⊥ : Subrepresentation I.representation) := by
          rw [h]
          trivial
        exact hx
      exact congrArg (fun k : A.representation.IntertwiningMap I.representation =>
        SmoothRep.ofHom k) hzero
    let : Nontrivial (Subrepresentation I.representation) := ⟨⟨⊥, ⊤, hbot_top⟩⟩
    apply IsSimpleOrder.of_forall_eq_top
    intro S hSbot
    by_contra hStop
    let P := SmoothRep.subrepresentation I S
    let Q := SmoothRep.quotient I S
    let a : P ⟶ I := SmoothRep.subtype I S
    let b : I ⟶ Q := SmoothRep.mkQ I S
    have ha : Function.Injective (SmoothRep.hom a) := SmoothRep.subtype_injective I S
    have hb : Function.Surjective (SmoothRep.hom b) := SmoothRep.mkQ_surjective I S
    have haneq : a ≫ j ≠ 0 := by
      intro hz
      apply hSbot
      apply Subrepresentation.toSubmodule_injective
      apply le_antisymm ?_ bot_le
      intro x hx
      have hxzero := congrArg (fun k : P ⟶ B => SmoothRep.hom k ⟨x, hx⟩) hz
      exact (map_eq_zero_iff (SmoothRep.hom j) hj).mp hxzero
    have hbneq : q ≫ b ≠ 0 := by
      intro hz
      apply hStop
      apply Subrepresentation.toSubmodule_injective
      apply top_unique
      intro x _
      obtain ⟨y, hy⟩ := hq x
      have hxzero := congrArg (fun k : A ⟶ Q => SmoothRep.hom k y) hz
      change (SmoothRep.hom b) (SmoothRep.hom q y) = 0 at hxzero
      rw [hy] at hxzero
      rw [← Submodule.ker_mkQ S.toSubmodule]
      exact hxzero
    obtain ⟨mP, hFP, hmP⟩ := hjpos P (a ≫ j) (hj.comp ha) haneq
    obtain ⟨mQ, hFQ, hmQ⟩ := hqpos Q (q ≫ b) (hb.comp hq) hbneq
    have hab : a ≫ b = 0 := by
      have hzero : SmoothRep.hom (a ≫ b) = 0 := by
        ext x
        have hx : x.1 ∈ LinearMap.ker S.toSubmodule.mkQ := by
          rw [Submodule.ker_mkQ]
          exact x.2
        exact hx
      exact congrArg (fun k : P.representation.IntertwiningMap Q.representation =>
        SmoothRep.ofHom k) hzero
    exact positive_zero_composite_impossible F I P Q a b ha hb hab τ mP mQ
      hFIone hFP hFQ hmP hmQ
  have hhead := multiplicityOneHeadCore F A τ hA ⟨I, hI, q, hq⟩ (by
    intro P hP q' hq'
    let := irreducible_carrier_nontrivial P hP
    apply hqpos P q' hq'
    intro hzero
    exact LinearMap.ne_zero_of_surjective hq'
      (congrArg (fun k : A ⟶ P => (SmoothRep.hom k).toLinearMap) hzero))
  have hsocle := multiplicityOneSocleCore F B τ hB ⟨I, hI, j, hj⟩ (by
    intro P hP j' hj'
    let := irreducible_carrier_nontrivial P hP
    apply hjpos P j' hj'
    intro hzero
    exact LinearMap.ne_zero_of_injective hj'
      (congrArg (fun k : P ⟶ B => (SmoothRep.hom k).toLinearMap) hzero))
  obtain ⟨W, _, _, π, hπ⟩ := hhead
  obtain ⟨W', _, _, π', hπ'⟩ := hsocle
  refine ⟨I, q, j, hq, hj, hfac, ⟨hI, SmoothRep.hom q, hq, ?_⟩,
    hI, SmoothRep.hom j, hj, ?_⟩
  · intro V _ _ ρ hρ r hr
    exact (hπ.headKernel_eq ρ hρ r hr).symm.trans
      (hπ.headKernel_eq I.representation hI (SmoothRep.hom q) hq)
  · intro V _ _ ρ hρ r hr
    exact (hπ'.socle_eq ρ hρ r hr).symm.trans
      (hπ'.socle_eq I.representation hI (SmoothRep.hom j) hj)

end Langlands.Classification
