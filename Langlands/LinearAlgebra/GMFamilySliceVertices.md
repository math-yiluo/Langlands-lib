# Affine vertices and transverse Levi flats

The affine slice has one inequality for each fine simple root. Its normal is the projection to the noncentral part of the coarse space and its offset is evaluation at the slice displacement. A basis of projected normals determines a Levi flat by the common kernel of the original normals in the fine space. The projection on its normal span is bijective because it maps the chosen fine roots to a coarse basis, so this flat has nonzero descent coefficient.

The unique intersection point of the flat with the slice evaluates each fine simple root to its affine slack. If a simple root outside the chosen basis also vanished there, general position would force it to annihilate the entire flat. Its fine normal would be in the span of the chosen subset of the fine simple-root basis, contradicting independence. Thus every affine basis intersection is regular for all its external inequalities.

Conversely, at the regular slice point of a transverse Levi flat in the closed chamber, the vanishing normals span the Levi normal space. These project to a basis. The inverse constructions are `basisTransverseLevi` and `activeSliceBasis`. Strict feasibility of a basis is equivalent to membership of its slice point in the closed chamber. The relative chamber has exactly the active fine simple roots, so the Gram-volume comparison and the pullback of the parameter give `weight_activeSliceBasis`.

The section and volume factors come from Arthur, *An introduction to the trace formula*, §17, printed pp. 99–100. The retained source is `arthur-ellwood-kottwitz-2005-harmonic-analysis-shimura`, SHA-256 `88ba9a23fa62e2f62f14af7a5a2a8ffb062be29fc4590bf39c60c173add0a8a7`.
