# Smooth algebra maps are open on complete-field points

Author: Worker 208.

`smoothAlgebraPointOpen` proves `SmoothAlgebraPointOpenStatement` in independent
universes for K, A and B. It uses the actual
smooth local normal form at the kernel of each field-valued point. The kernel is
prime, and smoothness gives the local smoothness hypothesis. Mathlib supplies a
principal localization of B standard etale over a finite polynomial algebra
over A. The proof installs the compatible scalar tower over K and identifies
restriction to A with the composite of standard etale restriction and relative
polynomial restriction. Both are open by the respective point-space results.

The chosen element is nonzero at the original point, so the actual localization
universal property lifts that point. The inverse image of any given open set
under localization restriction is open by continuity. Its image in A-points is
an open neighborhood of the restricted point and is contained in the original
open set's image. This proves openness without a finite-type condition over K.

The source and derived scope are recorded in the unchanged statement Markdown.
The general scheme comparison and chart gluing remain separate obligations.
The proof imports the published standard etale and relative polynomial results
by Lean name. It adds no characteristic, local compactness, nonarchimedean or
surjectivity hypothesis.
